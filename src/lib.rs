//use std::os::hermit::io::{AsFd, AsRawFd, FromRawFd};
extern crate hermit_abi as sys;
pub use socket::Socket;
use std::net::SocketAddr;
/*#[cfg(any(
    target_os = "android",
    target_os = "dragonfly",
    target_os = "freebsd",
    target_os = "fuchsia",
    target_os = "illumos",
    target_os = "ios",
    target_os = "visionos",
    target_os = "linux",
    target_os = "macos",
    target_os = "netbsd",
    target_os = "tvos",
    target_os = "watchos",
    target_os = "windows",
    target_os = "cygwin",
))]*/
pub use sockaddr::SockAddr;
pub use sockref::SockRef;
use std::time::Duration;
use sys::c_int;
pub mod sockaddr;
pub mod socket;
pub mod sockref;
pub mod system;
//pub mod sys;

macro_rules! impl_debug {
    (
        // Type name for which to implement `fmt::Debug`.
        $type: path,
        $(
            $(#[$target: meta])*
            // The flag(s) to check.
            // Need to specific the libc crate because Windows doesn't use
            // `libc` but `windows_sys`.
            $libc: ident :: $flag: ident
        ),+ $(,)*
    ) => {
        impl std::fmt::Debug for $type {
            fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
                let string = match self.0 {
                    $(
                        $(#[$target])*
                        $libc :: $flag => stringify!($flag),
                    )+
                    n => return write!(f, "{n}"),
                };
                f.write_str(string)
            }
        }
    };
}
impl_debug!(
    Domain,
    sys::AF_INET,
    sys::AF_INET6,
    sys::AF_VSOCK,
    sys::AF_UNSPEC, // = 0.
);
#[derive(Debug, Clone)]
pub struct TcpKeepalive {
    /*#[cfg_attr(
        any(target_os = "openbsd", target_os = "haiku", target_os = "vita"),
        allow(dead_code)
    )]*/
    time: Option<Duration>,
    /*#[cfg(not(any(
        target_os = "openbsd",
        target_os = "redox",
        target_os = "solaris",
        target_os = "nto",
        target_os = "espidf",
        target_os = "vita",
        target_os = "haiku",
    )))]
    interval: Option<Duration>,
    #[cfg(not(any(
        target_os = "openbsd",
        target_os = "redox",
        target_os = "solaris",
        target_os = "nto",
        target_os = "espidf",
        target_os = "vita",
        target_os = "haiku",
    )))]
    retries: Option<u32>,*/
}

impl TcpKeepalive {
    /// Returns a new, empty set of TCP keepalive parameters.
    #[allow(clippy::new_without_default)]
    pub const fn new() -> TcpKeepalive {
        TcpKeepalive {
            time: None,
            /*#[cfg(not(any(
                target_os = "openbsd",
                target_os = "redox",
                target_os = "solaris",
                target_os = "nto",
                target_os = "espidf",
                target_os = "vita",
                target_os = "haiku",
            )))]
            interval: None,*/
            /*#[cfg(not(any(
                target_os = "openbsd",
                target_os = "redox",
                target_os = "solaris",
                target_os = "nto",
                target_os = "espidf",
                target_os = "vita",
                target_os = "haiku",
            )))]
            retries: None,*/
        }
    }

    /// Set the amount of time after which TCP keepalive probes will be sent on
    /// idle connections.
    ///
    /// This will set `TCP_KEEPALIVE` on macOS and iOS, and
    /// `TCP_KEEPIDLE` on all other Unix operating systems, except
    /// OpenBSD and Haiku which don't support any way to set this
    /// option. On Windows, this sets the value of the `tcp_keepalive`
    /// struct's `keepalivetime` field.
    ///
    /// Some platforms specify this value in seconds, so sub-second
    /// specifications may be omitted.
    pub const fn with_time(self, time: Duration) -> Self {
        Self {
            time: Some(time),
            ..self
        }
    }
    /*
        /// Set the value of the `TCP_KEEPINTVL` option. On Windows, this sets the
        /// value of the `tcp_keepalive` struct's `keepaliveinterval` field.
        ///
        /// Sets the time interval between TCP keepalive probes.
        ///
        /// Some platforms specify this value in seconds, so sub-second
        /// specifications may be omitted.
        #[cfg(any(
            target_os = "android",
            target_os = "dragonfly",
            target_os = "freebsd",
            target_os = "fuchsia",
            target_os = "illumos",
            target_os = "ios",
            target_os = "visionos",
            target_os = "linux",
            target_os = "macos",
            target_os = "netbsd",
            target_os = "tvos",
            target_os = "watchos",
            target_os = "windows",
            target_os = "cygwin",
        ))]
        pub const fn with_interval(self, interval: Duration) -> Self {
            Self {
                interval: Some(interval),
                ..self
            }
        }
    */
    /*
     * /// Set the value of the `TCP_KEEPCNT` option.
     ///
     /// Set the maximum number of TCP keepalive probes that will be sent before
     /// dropping a connection, if TCP keepalive is enabled on this socket.
     * #[cfg(all(
        feature = "all",
        any(
            target_os = "android",
            target_os = "dragonfly",
            target_os = "freebsd",
            target_os = "fuchsia",
            target_os = "illumos",
            target_os = "ios",
            target_os = "visionos",
            target_os = "linux",
            target_os = "macos",
            target_os = "netbsd",
            target_os = "tvos",
            target_os = "watchos",
            target_os = "cygwin",
            target_os = "windows",
        )
    ))]
    pub const fn with_retries(self, retries: u32) -> Self {
        Self {
            retries: Some(retries),
            ..self
        }
    }*/
}
#[derive(Copy, Clone, Eq, PartialEq)]
pub struct Domain(c_int);

impl Domain {
    /// Domain for IPv4 communication, corresponding to `AF_INET`.
    pub const IPV4: Domain = Domain(sys::AF_INET);

    /// Domain for IPv6 communication, corresponding to `AF_INET6`.
    pub const IPV6: Domain = Domain(sys::AF_INET6);

    /// Domain for Unix socket communication, corresponding to `AF_UNIX`.
    //#[cfg(not(target_os = "hermit"))]
    //pub const UNIX: Domain = Domain(sys::AF_UNIX);

    /// Returns the correct domain for `address`.
    pub const fn for_address(address: SocketAddr) -> Domain {
        match address {
            SocketAddr::V4(_) => Domain::IPV4,
            SocketAddr::V6(_) => Domain::IPV6,
        }
    }
}

impl From<c_int> for Domain {
    fn from(d: c_int) -> Domain {
        Domain(d)
    }
}

impl From<Domain> for c_int {
    fn from(d: Domain) -> c_int {
        d.0
    }
}
#[derive(Copy, Clone, Eq, PartialEq)]
pub struct Type(c_int);

impl Type {
    /// Type corresponding to `SOCK_STREAM`.
    ///
    /// Used for protocols such as TCP.
    pub const STREAM: Type = Type(sys::SOCK_STREAM);

    /// Type corresponding to `SOCK_DGRAM`.
    ///
    /// Used for protocols such as UDP.
    pub const DGRAM: Type = Type(sys::SOCK_DGRAM);

    /* Unsupported by Hermit
       /// Type corresponding to `SOCK_DCCP`.
       ///
       /// Used for the DCCP protocol.
       //#[cfg(all(feature = "all", target_os = "linux"))]
       pub const DCCP: Type = Type(sys::SOCK_DCCP);

    /// Type corresponding to `SOCK_SEQPACKET`.
    //#[cfg(all(feature = "all", not(target_os = "espidf")))]
    pub const SEQPACKET: Type = Type(sys::SOCK_SEQPACKET);

    /// Type corresponding to `SOCK_RAW`.
    //#[cfg(all(feature = "all", not(any(target_os = "redox", target_os = "espidf"))))]
    pub const RAW: Type = Type(sys::SOCK_RAW);
    */
}

impl From<c_int> for Type {
    fn from(t: c_int) -> Type {
        Type(t)
    }
}

impl From<Type> for c_int {
    fn from(t: Type) -> c_int {
        t.0
    }
}

#[derive(Copy, Clone, Eq, PartialEq)]
pub struct Protocol(c_int);

impl Protocol {
    /* not supported by hermit
        /// Protocol corresponding to `ICMPv4`.
        pub const ICMPV4: Protocol = Protocol(sys::IPPROTO_ICMP);

        /// Protocol corresponding to `ICMPv6`.
        pub const ICMPV6: Protocol = Protocol(sys::IPPROTO_ICMPV6);
    */
    /// Protocol corresponding to `TCP`.
    pub const TCP: Protocol = Protocol(sys::IPPROTO_TCP);

    /// Protocol corresponding to `UDP`.
    pub const UDP: Protocol = Protocol(sys::IPPROTO_UDP);

    /* not supported by hermit
    /// Protocol corresponding to `MPTCP`.
    pub const MPTCP: Protocol = Protocol(sys::IPPROTO_MPTCP);

    /// Protocol corresponding to `DCCP`.
    //#[cfg(all(feature = "all", target_os = "linux"))]
    pub const DCCP: Protocol = Protocol(sys::IPPROTO_DCCP);

    /// Protocol corresponding to `SCTP`.
    //#[cfg(all(feature = "all", any(target_os = "freebsd", target_os = "linux")))]
    pub const SCTP: Protocol = Protocol(sys::IPPROTO_SCTP);

    /// Protocol corresponding to `UDPLITE`.
    #[cfg(all(
        feature = "all",
        any(
            target_os = "android",
            target_os = "freebsd",
            target_os = "fuchsia",
            target_os = "linux",
        )
    ))]
    pub const UDPLITE: Protocol = Protocol(sys::IPPROTO_UDPLITE);

    /// Protocol corresponding to `DIVERT`.
    //#[cfg(all(feature = "all", any(target_os = "freebsd", target_os = "openbsd")))]
    pub const DIVERT: Protocol = Protocol(sys::IPPROTO_DIVERT);
    */
}

impl From<c_int> for Protocol {
    fn from(p: c_int) -> Protocol {
        Protocol(p)
    }
}

impl From<Protocol> for c_int {
    fn from(p: Protocol) -> c_int {
        p.0
    }
}
