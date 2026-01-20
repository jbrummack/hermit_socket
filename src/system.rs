use std::cmp::min;
use std::mem::MaybeUninit;
use std::net::{Ipv4Addr, Ipv6Addr, Shutdown};
use std::{io, mem, ptr};
extern crate hermit_abi as sys;
macro_rules! syscall {
    ($fn: ident ( $($arg: expr),* $(,)* ) ) => {{
        #[allow(unused_unsafe)]
        let res = unsafe { sys::$fn($($arg, )*) };
        if res == -1 {
            Err(std::io::Error::last_os_error())
        } else {
            Ok(res)
        }
    }};
}

use std::os::hermit::io::{AsFd, AsRawFd, BorrowedFd, FromRawFd, IntoRawFd, OwnedFd, RawFd};
use std::time::{Duration, Instant};
use sys::{in_addr, in6_addr};
pub(crate) type Socket = OwnedFd;
pub(crate) type RawSocket = sys::c_int;

pub(crate) fn from_in_addr(in_addr: in_addr) -> Ipv4Addr {
    Ipv4Addr::from(in_addr.s_addr.to_ne_bytes())
}
pub(crate) fn from_in6_addr(addr: in6_addr) -> Ipv6Addr {
    Ipv6Addr::from(addr.s6_addr)
}
pub(crate) const fn to_in_addr(addr: &Ipv4Addr) -> in_addr {
    // `s_addr` is stored as BE on all machines, and the array is in BE order.
    // So the native endian conversion method is used so that it's never
    // swapped.
    in_addr {
        s_addr: u32::from_ne_bytes(addr.octets()),
    }
}
pub(crate) const fn to_in6_addr(addr: &Ipv6Addr) -> in6_addr {
    in6_addr {
        s6_addr: addr.octets(),
    }
}

impl AsFd for crate::Socket {
    fn as_fd(&self) -> BorrowedFd<'_> {
        // SAFETY: lifetime is bound by self.
        unsafe { BorrowedFd::borrow_raw(self.as_raw()) }
    }
}

impl AsRawFd for crate::Socket {
    fn as_raw_fd(&self) -> RawFd {
        self.as_raw()
    }
}

impl From<crate::Socket> for OwnedFd {
    fn from(sock: crate::Socket) -> OwnedFd {
        // SAFETY: sock.into_raw() always returns a valid fd.
        unsafe { OwnedFd::from_raw_fd(sock.into_raw()) }
    }
}

impl IntoRawFd for crate::Socket {
    fn into_raw_fd(self) -> c_int {
        self.into_raw()
    }
}

impl From<OwnedFd> for crate::Socket {
    fn from(fd: OwnedFd) -> crate::Socket {
        // SAFETY: `OwnedFd` ensures the fd is valid.
        unsafe { crate::Socket::from_raw_fd(fd.into_raw_fd()) }
    }
}

impl FromRawFd for crate::Socket {
    unsafe fn from_raw_fd(fd: c_int) -> crate::Socket {
        crate::Socket::from_raw(fd)
    }
}

pub(crate) unsafe fn socket_from_raw(socket: RawSocket) -> Socket {
    Socket::from_raw_fd(socket)
}

pub(crate) fn socket_as_raw(socket: &Socket) -> RawSocket {
    socket.as_fd().as_raw_fd()
}

pub(crate) fn socket_into_raw(socket: Socket) -> RawSocket {
    socket.into_raw_fd()
}
use sys::c_int;

use crate::sockaddr::SockAddr;
pub(crate) fn socket(family: c_int, ty: c_int, protocol: c_int) -> io::Result<RawSocket> {
    syscall!(socket(family, ty, protocol))
}
/*pub(crate) fn socketpair(family: c_int, ty: c_int, protocol: c_int) -> io::Result<[RawSocket; 2]> {
    let mut fds = [0, 0];
    syscall!(socketpair(family, ty, protocol, fds.as_mut_ptr())).map(|_| fds)
}*/

pub(crate) fn bind(fd: RawSocket, addr: &SockAddr) -> io::Result<()> {
    syscall!(bind(
        fd,
        addr.as_ptr().cast::<sys::sockaddr>(),
        addr.len() as _
    ))
    .map(|_| ())
}

pub(crate) fn connect(fd: RawSocket, addr: &SockAddr) -> io::Result<()> {
    syscall!(connect(
        fd,
        addr.as_ptr().cast::<sys::sockaddr>(),
        addr.len()
    ))
    .map(|_| ())
}
pub(crate) fn poll_connect(socket: &crate::Socket, timeout: Duration) -> io::Result<()> {
    let start = Instant::now();

    let mut pollfd = sys::pollfd {
        fd: socket.as_raw(),
        events: sys::POLLIN | sys::POLLOUT,
        revents: 0,
    };

    loop {
        let elapsed = start.elapsed();
        if elapsed >= timeout {
            return Err(io::ErrorKind::TimedOut.into());
        }

        let timeout = (timeout - elapsed).as_millis();
        let timeout = timeout.clamp(1, c_int::MAX as u128) as c_int;

        match syscall!(poll(&mut pollfd, 1, timeout)) {
            Ok(0) => return Err(io::ErrorKind::TimedOut.into()),
            Ok(_) => {
                // Error or hang up indicates an error (or failure to connect).
                if (pollfd.revents & sys::POLLHUP) != 0 || (pollfd.revents & sys::POLLERR) != 0 {
                    match socket.take_error() {
                        Ok(Some(err)) | Err(err) => return Err(err),
                        Ok(None) => {
                            return Err(io::Error::new(
                                io::ErrorKind::Other,
                                "no error set after POLLHUP",
                            ));
                        }
                    }
                }
                return Ok(());
            }
            // Got interrupted, try again.
            Err(ref err) if err.kind() == io::ErrorKind::Interrupted => continue,
            Err(err) => return Err(err),
        }
    }
}
pub(crate) fn listen(fd: RawSocket, backlog: c_int) -> io::Result<()> {
    syscall!(listen(fd, backlog)).map(|_| ())
}

pub(crate) fn accept(fd: RawSocket) -> io::Result<(RawSocket, SockAddr)> {
    // Safety: `accept` initialises the `SockAddr` for us.
    unsafe { SockAddr::try_init(|storage, len| syscall!(accept(fd, storage.cast(), len))) }
}

pub(crate) fn getsockname(fd: RawSocket) -> io::Result<SockAddr> {
    // Safety: `accept` initialises the `SockAddr` for us.
    unsafe { SockAddr::try_init(|storage, len| syscall!(getsockname(fd, storage.cast(), len))) }
        .map(|(_, addr)| addr)
}

pub(crate) fn getpeername(fd: RawSocket) -> io::Result<SockAddr> {
    // Safety: `accept` initialises the `SockAddr` for us.
    unsafe { SockAddr::try_init(|storage, len| syscall!(getpeername(fd, storage.cast(), len))) }
        .map(|(_, addr)| addr)
}

pub(crate) fn shutdown(fd: RawSocket, how: Shutdown) -> io::Result<()> {
    let how = match how {
        Shutdown::Write => sys::SHUT_WR,
        Shutdown::Read => sys::SHUT_RD,
        Shutdown::Both => sys::SHUT_RDWR,
    };
    syscall!(shutdown(fd, how)).map(|_| ())
}
const MAX_BUF_LEN: usize = sys::c_int::MAX as usize - 1;

pub(crate) fn recv(fd: RawSocket, buf: &mut [MaybeUninit<u8>], flags: c_int) -> io::Result<usize> {
    syscall!(recv(
        fd,
        buf.as_mut_ptr().cast(),
        min(buf.len(), MAX_BUF_LEN),
        flags,
    ))
    .map(|n| n as usize)
}

pub(crate) fn recv_from(
    fd: RawSocket,
    buf: &mut [MaybeUninit<u8>],
    flags: c_int,
) -> io::Result<(usize, SockAddr)> {
    // Safety: `recvfrom` initialises the `SockAddr` for us.
    unsafe {
        SockAddr::try_init(|addr, addrlen| {
            syscall!(recvfrom(
                fd,
                buf.as_mut_ptr().cast(),
                min(buf.len(), MAX_BUF_LEN),
                flags,
                addr.cast(),
                addrlen
            ))
            .map(|n| n as usize)
        })
    }
}

pub(crate) fn peek_sender(fd: RawSocket) -> io::Result<SockAddr> {
    // Unix-like platforms simply truncate the returned data, so this implementation is trivial.
    // However, for Windows this requires suppressing the `WSAEMSGSIZE` error,
    // so that requires a different approach.
    // NOTE: macOS does not populate `sockaddr` if you pass a zero-sized buffer.
    let (_, sender) = recv_from(fd, &mut [MaybeUninit::uninit(); 8], sys::MSG_PEEK)?;
    Ok(sender)
}
/// Caller must ensure `T` is the correct type for `opt` and `val`.
pub(crate) unsafe fn getsockopt<T>(fd: RawSocket, opt: c_int, val: c_int) -> io::Result<T> {
    let mut payload: MaybeUninit<T> = MaybeUninit::uninit();
    let mut len = size_of::<T>() as sys::socklen_t;
    syscall!(getsockopt(
        fd,
        opt,
        val,
        payload.as_mut_ptr().cast(),
        &mut len,
    ))
    .map(|_| {
        debug_assert_eq!(len as usize, size_of::<T>());
        // Safety: `getsockopt` initialised `payload` for us.
        unsafe { payload.assume_init() }
    })
}

/// Caller must ensure `T` is the correct type for `opt` and `val`.
pub(crate) unsafe fn setsockopt<T>(
    fd: RawSocket,
    opt: c_int,
    val: c_int,
    payload: T,
) -> io::Result<()> {
    let payload = ptr::addr_of!(payload).cast();
    syscall!(setsockopt(
        fd,
        opt,
        val,
        payload,
        mem::size_of::<T>() as sys::socklen_t,
    ))
    .map(|_| ())
}
pub(crate) fn send(fd: RawSocket, buf: &[u8], flags: c_int) -> io::Result<usize> {
    syscall!(send(
        fd,
        buf.as_ptr().cast(),
        min(buf.len(), MAX_BUF_LEN),
        flags,
    ))
    .map(|n| n as usize)
}
pub(crate) fn send_to(
    fd: RawSocket,
    buf: &[u8],
    addr: &SockAddr,
    flags: c_int,
) -> io::Result<usize> {
    syscall!(sendto(
        fd,
        buf.as_ptr().cast(),
        min(buf.len(), MAX_BUF_LEN),
        flags,
        addr.as_ptr().cast::<sys::sockaddr>(),
        addr.len(),
    ))
    .map(|n| n as usize)
}
/*pub(crate) fn timeout_opt(fd: RawSocket, opt: c_int, val: c_int) -> io::Result<Option<Duration>> {
    unsafe { sys::getsockopt(fd, opt, val).map(from_timeval) }
}*/

const fn from_timeval(duration: sys::timeval) -> Option<Duration> {
    if duration.tv_sec == 0 && duration.tv_usec == 0 {
        None
    } else {
        let sec = duration.tv_sec as u64;
        let nsec = (duration.tv_usec as u32) * 1000;
        Some(Duration::new(sec, nsec))
    }
}

/// Wrapper around `setsockopt` to deal with platform specific timeouts.
/*pub(crate) fn set_timeout_opt(
    fd: RawSocket,
    opt: c_int,
    val: c_int,
    duration: Option<Duration>,
) -> io::Result<()> {
    let duration = into_timeval(duration);
    unsafe { sys::setsockopt(fd, opt, val, duration) }
}*/

fn into_timeval(duration: Option<Duration>) -> sys::timeval {
    match duration {
        // https://github.com/rust-lang/libc/issues/1848
        #[cfg_attr(target_env = "musl", allow(deprecated))]
        Some(duration) => sys::timeval {
            tv_sec: min(duration.as_secs(), sys::time_t::MAX as u64) as sys::time_t,
            tv_usec: duration.subsec_micros() as sys::suseconds_t,
        },
        None => sys::timeval {
            tv_sec: 0,
            tv_usec: 0,
        },
    }
}
pub(crate) fn nonblocking(fd: RawSocket) -> io::Result<bool> {
    //let file_status_flags = sys::fcntl_get(fd, sys::F_GETFL)?;
    //Ok((file_status_flags & sys::O_NONBLOCK) != 0)
    todo!()
}

/*fn fcntl_get(fd: RawSocket, cmd: c_int) -> io::Result<c_int> {
    syscall!(fcntl(fd, cmd))
}

pub(crate) fn set_nonblocking(fd: RawSocket, nonblocking: bool) -> io::Result<()> {
    if nonblocking {
        fcntl_add(fd, sys::F_GETFL, libc::F_SETFL, libc::O_NONBLOCK)
    } else {
        fcntl_remove(fd, libc::F_GETFL, libc::F_SETFL, libc::O_NONBLOCK)
    }
}*/
/*pub(crate) fn try_clone(fd: RawSocket) -> io::Result<RawSocket> {
    syscall!(fcntl(fd, sys::F_DUPFD_CLOEXEC, 0))
}*/

/*fn fcntl_get(fd: Socket, cmd: c_int) -> io::Result<c_int> {
    Ok(unsafe { sys::fcntl(fd, cmd, 0) })
}*/
#[test]
fn in_addr_convertion() {
    let ip = Ipv4Addr::new(127, 0, 0, 1);
    let raw = to_in_addr(&ip);
    // NOTE: `in_addr` is packed on NetBSD and it's unsafe to borrow.
    let a = raw.s_addr;
    assert_eq!(a, u32::from_ne_bytes([127, 0, 0, 1]));
    assert_eq!(from_in_addr(raw), ip);

    let ip = Ipv4Addr::new(127, 34, 4, 12);
    let raw = to_in_addr(&ip);
    let a = raw.s_addr;
    assert_eq!(a, u32::from_ne_bytes([127, 34, 4, 12]));
    assert_eq!(from_in_addr(raw), ip);
}

#[test]
fn in6_addr_convertion() {
    let ip = Ipv6Addr::new(0x2000, 1, 2, 3, 4, 5, 6, 7);
    let raw = to_in6_addr(&ip);
    let want = [32, 0, 0, 1, 0, 2, 0, 3, 0, 4, 0, 5, 0, 6, 0, 7];
    assert_eq!(raw.s6_addr, want);
    assert_eq!(from_in6_addr(raw), ip);
}
