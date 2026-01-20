use crate::Domain;
use crate::Protocol;
use crate::TcpKeepalive;
use crate::Type;
use crate::{sockaddr::SockAddr, system};
use hermit_abi::c_int;
use std::mem::MaybeUninit;
use std::net::Ipv4Addr;
use std::net::Ipv6Addr;
use std::net::Shutdown;
use std::{io::Result, time::Duration};
//use crate::system:;
//extern crate hermit_abi as libc;

//use std::os::hermit::io::{FromRawFd, IntoRawFd};
/// Owned wrapper around a system socket.
pub struct Socket {
    inner: system::Socket,
}
impl Socket {
    pub(crate) fn as_raw(&self) -> system::RawSocket {
        system::socket_as_raw(&self.inner)
    }

    pub(crate) fn into_raw(self) -> system::RawSocket {
        system::socket_into_raw(self.inner)
    }
    pub(crate) fn from_raw(raw: system::RawSocket) -> Socket {
        Socket {
            // SAFETY: the caller must ensure that `raw` is a valid file
            // descriptor, but when it isn't it could return I/O errors, or
            // potentially close a fd it doesn't own. All of that isn't memory
            // unsafe, so it's not desired but never memory unsafe or causes UB.
            inner: unsafe { system::socket_from_raw(raw) },
        }
    }
    pub fn new(domain: Domain, ty: Type, protocol: Option<Protocol>) -> Result<Socket> {
        let ty = set_common_type(ty);
        Socket::new_raw(domain, ty, protocol).and_then(set_common_flags)
    }
    pub fn new_raw(domain: Domain, ty: Type, protocol: Option<Protocol>) -> Result<Socket> {
        let protocol = protocol.map_or(0, |p| p.0);
        system::socket(domain.0, ty.0, protocol).map(Socket::from_raw)
    }
    /* not supported in hermit
    pub fn pair(
        domain: Domain,
        ty: Type,
        protocol: Option<Protocol>,
    ) -> io::Result<(Socket, Socket)> {
        let ty = set_common_type(ty);
        let (a, b) = Socket::pair_raw(domain, ty, protocol)?;
        let a = set_common_flags(a)?;
        let b = set_common_flags(b)?;
        Ok((a, b))
    }

    pub fn pair_raw(
        domain: Domain,
        ty: Type,
        protocol: Option<Protocol>,
    ) -> io::Result<(Socket, Socket)> {
        let protocol = protocol.map_or(0, |p| p.0);
        system::socketpair(domain.0, ty.0, protocol)
            .map(|[a, b]| (Socket::from_raw(a), Socket::from_raw(b)))
    } */
    pub fn bind(&self, address: &SockAddr) -> Result<()> {
        system::bind(self.as_raw(), address)
    }
    pub fn connect(&self, address: &SockAddr) -> Result<()> {
        unsafe { system::connect(self.as_raw(), address) }
    }
    pub fn connect_timeout(&self, addr: &SockAddr, timeout: Duration) -> Result<()> {
        self.set_nonblocking(true)?;
        let res = self.connect(addr);
        self.set_nonblocking(false)?;

        match res {
            Ok(()) => return Ok(()),
            Err(ref e) if e.kind() == std::io::ErrorKind::WouldBlock => {}
            #[cfg(unix)]
            Err(ref e) if e.raw_os_error() == Some(sys::EINPROGRESS) => {}
            Err(e) => return Err(e),
        }

        system::poll_connect(self, timeout)
    }
    pub fn listen(&self, backlog: c_int) -> Result<()> {
        system::listen(self.as_raw(), backlog)
    }
    pub fn accept(&self) -> Result<(Socket, SockAddr)> {
        let (socket, addr) = self.accept_raw()?;
        let socket = set_common_accept_flags(socket)?;
        Ok((socket, addr))
    }
    pub fn accept_raw(&self) -> Result<(Socket, SockAddr)> {
        system::accept(self.as_raw()).map(|(inner, addr)| (Socket::from_raw(inner), addr))
    }
    pub fn local_addr(&self) -> Result<SockAddr> {
        system::getsockname(self.as_raw())
    }

    pub fn peer_addr(&self) -> Result<SockAddr> {
        unsafe { sys::getpeername(self.as_raw()) }
    }

    pub fn r#type(&self) -> Result<Type> {
        unsafe { sys::getsockopt::<c_int>(self.as_raw(), sys::SOL_SOCKET, sys::SO_TYPE).map(Type) }
    }

    /*pub fn try_clone(&self) -> Result<Socket> {
        system::try_clone(self.as_raw()).map(Socket::from_raw)
    }*/

    pub fn nonblocking(&self) -> Result<bool> {
        system::nonblocking(self.as_raw())
    }
    //Available on crate feature all and Unix only.

    pub fn set_nonblocking(&self, nonblocking: bool) -> Result<()> {
        todo!()
    }

    pub fn shutdown(&self, how: Shutdown) -> Result<()> {
        system::shutdown(self.as_raw(), how)
    }

    pub fn recv(&self, buf: &mut [MaybeUninit<u8>]) -> Result<usize> {
        self.recv_with_flags(buf, 0)
    }

    /*pub fn recv_out_of_band(&self, buf: &mut [MaybeUninit<u8>]) -> Result<usize> {
        //self.recv_with_flags(buf, system::MSG_OOB)
        //todo!()
    }*/

    pub fn recv_with_flags(&self, buf: &mut [MaybeUninit<u8>], flags: c_int) -> Result<usize> {
        system::recv(self.as_raw(), buf, flags)
    }
    /*Available on non-Redox only.
    pub fn recv_vectored(&self, bufs: &mut [MaybeUninitSlice<'_>]) -> Result<(usize, RecvFlags)> {
        todo!()
    }

    //Available on non-Redox only.
    pub fn recv_vectored_with_flags(
        &self,
        bufs: &mut [MaybeUninitSlice<'_>],
        flags: c_int,
    ) -> Result<(usize, RecvFlags)> {
        todo!()
    }
    */
    pub fn peek(&self, buf: &mut [MaybeUninit<u8>]) -> Result<usize> {
        self.recv_with_flags(buf, sys::MSG_PEEK)
    }

    pub fn recv_from(&self, buf: &mut [MaybeUninit<u8>]) -> Result<(usize, SockAddr)> {
        self.recv_from_with_flags(buf, 0)
    }

    pub fn recv_from_with_flags(
        &self,
        buf: &mut [MaybeUninit<u8>],
        flags: c_int,
    ) -> Result<(usize, SockAddr)> {
        system::recv_from(self.as_raw(), buf, flags)
    }
    /*Available on non-Redox only.
    pub fn recv_from_vectored(
        &self,
        bufs: &mut [MaybeUninitSlice<'_>],
    ) -> Result<(usize, RecvFlags, SockAddr)> {
        todo!()
    }

    //Available on non-Redox only.
    pub fn recv_from_vectored_with_flags(
        &self,
        bufs: &mut [MaybeUninitSlice<'_>],
        flags: c_int,
    ) -> Result<(usize, RecvFlags, SockAddr)> {
        todo!()
    }
    */

    pub fn peek_from(&self, buf: &mut [MaybeUninit<u8>]) -> Result<(usize, SockAddr)> {
        self.recv_from_with_flags(buf, sys::MSG_PEEK)
    }

    pub fn peek_sender(&self) -> Result<SockAddr> {
        system::peek_sender(self.as_raw())
    }
    /*Available on Unix and non-Redox only.
    pub fn recvmsg(&self, msg: &mut MsgHdrMut<'_, '_, '_>, flags: c_int) -> Result<usize> {
        todo!()
    }
    */

    pub fn send(&self, buf: &[u8]) -> Result<usize> {
        self.send_with_flags(buf, 0)
    }

    pub fn send_with_flags(&self, buf: &[u8], flags: c_int) -> Result<usize> {
        system::send(self.as_raw(), buf, flags)
    }
    /*Available on non-Redox only.
    pub fn send_vectored(&self, bufs: &[IoSlice<'_>]) -> Result<usize> {
        todo!()
    }


    pub fn send_vectored_with_flags(&self, bufs: &[IoSlice<'_>], flags: c_int) -> Result<usize> {
        todo!()
    }
    */

    /* redox only
    pub fn send_out_of_band(&self, buf: &[u8]) -> Result<usize> {
        todo!()
    }*/

    pub fn send_to(&self, buf: &[u8], addr: &SockAddr) -> Result<usize> {
        self.send_to_with_flags(buf, addr, 0)
    }

    pub fn send_to_with_flags(&self, buf: &[u8], addr: &SockAddr, flags: c_int) -> Result<usize> {
        system::send_to(self.as_raw(), buf, addr, flags)
    }
}
///Socket options get/set using SOL_SOCKET
impl Socket {
    pub fn broadcast(&self) -> Result<bool> {
        todo!()
    }

    pub fn set_broadcast(&self, broadcast: bool) -> Result<()> {
        todo!()
    }
    pub fn take_error(&self) -> Result<Option<std::io::Error>> {
        match unsafe { system::getsockopt::<c_int>(self.as_raw(), sys::SOL_SOCKET, sys::SO_ERROR) }
        {
            Ok(0) => Ok(None),
            Ok(errno) => Ok(Some(std::io::Error::from_raw_os_error(errno))),
            Err(err) => Err(err),
        }
    }

    pub fn keepalive(&self) -> Result<bool> {
        todo!()
    }

    pub fn set_keepalive(&self, keepalive: bool) -> Result<()> {
        todo!()
    }

    pub fn linger(&self) -> Result<Option<Duration>> {
        todo!()
    }

    pub fn set_linger(&self, linger: Option<Duration>) -> Result<()> {
        todo!()
    }
    pub fn recv_buffer_size(&self) -> Result<usize> {
        todo!()
    }
    pub fn set_recv_buffer_size(&self, size: usize) -> Result<()> {
        todo!()
    }
    pub fn read_timeout(&self) -> Result<Option<Duration>> {
        todo!()
    }
    pub fn set_read_timeout(&self, duration: Option<Duration>) -> Result<()> {
        todo!()
    }
    pub fn reuse_address(&self) -> Result<bool> {
        todo!()
    }
    pub fn set_reuse_address(&self, reuse: bool) -> Result<()> {
        todo!()
    }
    pub fn send_buffer_size(&self) -> Result<usize> {
        todo!()
    }
    pub fn set_send_buffer_size(&self, size: usize) -> Result<()> {
        todo!()
    }
    pub fn write_timeout(&self) -> Result<Option<Duration>> {
        todo!()
    }
    pub fn set_write_timeout(&self, duration: Option<Duration>) -> Result<()> {
        todo!()
    }
}
///Socket options for IPv4 sockets, get/set using IPPROTO_IP or SOL_IP
impl Socket {
    pub fn join_multicast_v4(&self, multiaddr: &Ipv4Addr, interface: &Ipv4Addr) -> Result<()> {
        let mreq = sys::ip_mreq {
            imr_multiaddr: system::to_in_addr(multiaddr),
            imr_interface: system::to_in_addr(interface),
        };
        unsafe { system::setsockopt(self.as_raw(), sys::IPPROTO_IP, sys::IP_ADD_MEMBERSHIP, mreq) }
    }
    pub fn leave_multicast_v4(&self, multiaddr: &Ipv4Addr, interface: &Ipv4Addr) -> Result<()> {
        let mreq = sys::ip_mreq {
            imr_multiaddr: system::to_in_addr(multiaddr),
            imr_interface: system::to_in_addr(interface),
        };
        unsafe {
            system::setsockopt(
                self.as_raw(),
                sys::IPPROTO_IP,
                sys::IP_DROP_MEMBERSHIP,
                mreq,
            )
        }
    }
    /* Not supported in hermit
    pub fn multicast_if_v4(&self) -> Result<Ipv4Addr> {
        unsafe {
            system::getsockopt(self.as_raw(), sys::IPPROTO_IP, sys::IP_MULTICAST_IF)
                .map(system::from_in_addr)
        }
    }
    pub fn set_multicast_if_v4(&self, interface: &Ipv4Addr) -> Result<()> {
        todo!()
    }
    pub fn multicast_loop_v4(&self) -> Result<bool> {
        todo!()
    }
    pub fn set_multicast_loop_v4(&self, loop_v4: bool) -> Result<()> {
        todo!()
    }
    pub fn multicast_ttl_v4(&self) -> Result<u32> {
        todo!()
    }
    pub fn set_multicast_ttl_v4(&self, ttl: u32) -> Result<()> {
        todo!()
    }
    pub fn ttl_v4(&self) -> Result<u32> {
        todo!()
    }
    pub fn set_ttl_v4(&self, ttl: u32) -> Result<()> {
        todo!()
    }*/
}
///Socket options for IPv6 sockets, get/set using IPPROTO_IPV6 or SOL_IPV6
impl Socket {
    pub fn join_multicast_v6(&self, multiaddr: &Ipv6Addr, interface: u32) -> Result<()> {
        let mreq = sys::ipv6_mreq {
            ipv6mr_multiaddr: system::to_in6_addr(multiaddr),
            // NOTE: some OSs use `c_int`, others use `c_uint`.
            ipv6mr_interface: interface as _,
        };
        unsafe {
            system::setsockopt(
                self.as_raw(),
                sys::IPPROTO_IPV6,
                sys::IPV6_ADD_MEMBERSHIP,
                mreq,
            )
        }
    }
    pub fn leave_multicast_v6(&self, multiaddr: &Ipv6Addr, interface: u32) -> Result<()> {
        let mreq = sys::ipv6_mreq {
            ipv6mr_multiaddr: system::to_in6_addr(multiaddr),
            // NOTE: some OSs use `c_int`, others use `c_uint`.
            ipv6mr_interface: interface as _,
        };
        unsafe {
            system::setsockopt(
                self.as_raw(),
                sys::IPPROTO_IPV6,
                sys::IPV6_DROP_MEMBERSHIP,
                mreq,
            )
        }
    }
    /*
    not supported in hermit
     pub fn multicast_if_v6(&self) -> Result<Ipv6Addr> {
        todo!()
    }
    pub fn set_multicast_if_v6(&self, interface: &Ipv6Addr) -> Result<()> {
        todo!()
    }
    pub fn multicast_loop_v6(&self) -> Result<bool> {
        todo!()
    }
    pub fn set_multicast_loop_v6(&self, loop_v4: bool) -> Result<()> {
        todo!()
    }
    pub fn multicast_ttl_v6(&self) -> Result<u32> {
        todo!()
    }
    pub fn set_multicast_ttl_v6(&self, ttl: u32) -> Result<()> {
        todo!()
    }
    pub fn ttl_v6(&self) -> Result<u32> {
        todo!()
    }
    pub fn set_ttl_v6(&self, ttl: u32) -> Result<()> {
        todo!()
    }*/
}

///Socket options for TCP sockets, get/set using IPPROTO_TCP.
/// Doesnt do anything on hermit
impl Socket {
    pub fn set_tcp_keepalive(&self, params: &TcpKeepalive) -> Result<()> {
        //todo!()
        Ok(())
    }
    /*pub fn tcp_nodelay(&self) -> Result<bool> {
        todo!()
    }*/
    /*pub fn set_tcp_nodelay(&self, nodelay: bool) -> Result<()> {
        todo!()
    }*/
}
/// Set `SOCK_CLOEXEC` and `NO_HANDLE_INHERIT` on the `ty`pe on platforms that
/// support it.
/// Does nothing on hermit
#[inline(always)]
const fn set_common_type(ty: Type) -> Type {
    //let ty = ty._cloexec();

    ty
}

/// Set `FD_CLOEXEC` and `NOSIGPIPE` on the `socket` for platforms that need it.
///
/// Sockets created via `accept` should use `set_common_accept_flags` instead.
/// Does nothing on hermit
fn set_common_flags(socket: Socket) -> Result<Socket> {
    // On platforms that don't have `SOCK_CLOEXEC` use `FD_CLOEXEC`.
    //socket._set_cloexec(true)?;

    Ok(socket)
}
/// Does nothing on hermit
fn set_common_accept_flags(socket: Socket) -> Result<Socket> {
    // On platforms that don't have `SOCK_CLOEXEC` use `FD_CLOEXEC`.

    //
    // socket._set_cloexec(true)?;

    Ok(socket)
}
