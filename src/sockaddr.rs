extern crate hermit_abi as sys;
use crate::{
    Domain,
    system::{from_in_addr, from_in6_addr, to_in_addr, to_in6_addr},
};
use std::{
    mem,
    net::{SocketAddr, SocketAddrV4, SocketAddrV6},
    ptr,
};
use sys::{
    AF_INET, AF_INET6, c_int, sa_family_t, sockaddr_in, sockaddr_in6, sockaddr_storage, socklen_t,
};
/// Rust version of the [`sockaddr_storage`] type.
///
/// This type is intended to be used with with direct calls to the `getsockname` syscall. See the
/// documentation of [`SockAddr::new`] for examples.
///
/// This crate defines its own `sockaddr_storage` type to avoid semver concerns with upgrading
/// `windows-sys`.
#[repr(transparent)]
pub struct SockAddrStorage {
    storage: sockaddr_storage,
}

impl SockAddrStorage {
    /// Construct a new storage containing all zeros.
    #[inline]
    pub fn zeroed() -> Self {
        // SAFETY: All zeros is valid for this type.
        unsafe { mem::zeroed() }
    }

    /// Returns the size of this storage.
    #[inline]
    pub fn size_of(&self) -> socklen_t {
        size_of::<Self>() as socklen_t
    }

    /// View this type as another type.
    ///
    /// # Safety
    ///
    /// The type `T` must be one of the `sockaddr_*` types defined by this platform.
    ///
    /// # Examples
    /// ```
    /// # #[allow(dead_code)]
    /// # #[cfg(unix)] mod unix_example {
    /// # use core::mem::size_of;
    /// use libc::sockaddr_storage;
    /// use socket2::{SockAddr, SockAddrStorage, socklen_t};
    ///
    /// fn from_sockaddr_storage(recv_address: &sockaddr_storage) -> SockAddr {
    ///     let mut storage = SockAddrStorage::zeroed();
    ///     let libc_address = unsafe { storage.view_as::<sockaddr_storage>() };
    ///     *libc_address = *recv_address;
    ///     unsafe { SockAddr::new(storage, size_of::<sockaddr_storage>() as socklen_t) }
    /// }
    /// # }
    /// ```
    #[inline]
    pub fn view_as<T>(&mut self) -> &mut T {
        assert!(size_of::<T>() <= size_of::<Self>());
        // SAFETY: This type is repr(transparent) over `sockaddr_storage` and `T` is one of the
        // `sockaddr_*` types defined by this platform.
        unsafe { &mut *(self as *mut Self as *mut T) }
    }
}

impl std::fmt::Debug for SockAddrStorage {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        f.debug_struct("sockaddr_storage")
            .field("ss_family", &self.storage.ss_family)
            .finish_non_exhaustive()
    }
}

pub struct SockAddr {
    storage: sockaddr_storage,
    len: socklen_t,
}
impl From<SocketAddrV4> for SockAddr {
    fn from(addr: SocketAddrV4) -> SockAddr {
        // SAFETY: a `sockaddr_storage` of all zeros is valid.
        let mut storage = unsafe { mem::zeroed::<sockaddr_storage>() };
        let len = {
            let storage = unsafe { &mut *ptr::addr_of_mut!(storage).cast::<sockaddr_in>() };
            storage.sin_family = AF_INET as sa_family_t;
            storage.sin_port = addr.port().to_be();
            storage.sin_addr = to_in_addr(addr.ip());
            storage.sin_zero = Default::default();
            mem::size_of::<sockaddr_in>() as socklen_t
        };

        SockAddr { storage, len }
    }
}
impl PartialEq for SockAddr {
    fn eq(&self, other: &Self) -> bool {
        self.as_bytes() == other.as_bytes()
    }
}

impl Eq for SockAddr {}

impl std::hash::Hash for SockAddr {
    fn hash<H: std::hash::Hasher>(&self, state: &mut H) {
        self.as_bytes().hash(state);
    }
}
impl From<SocketAddrV6> for SockAddr {
    fn from(addr: SocketAddrV6) -> SockAddr {
        // SAFETY: a `sockaddr_storage` of all zeros is valid.
        let mut storage = unsafe { mem::zeroed::<sockaddr_storage>() };
        let len = {
            let storage = unsafe { &mut *ptr::addr_of_mut!(storage).cast::<sockaddr_in6>() };
            storage.sin6_family = AF_INET6 as sa_family_t;
            storage.sin6_port = addr.port().to_be();
            storage.sin6_addr = to_in6_addr(addr.ip());
            storage.sin6_flowinfo = addr.flowinfo();
            {
                storage.sin6_scope_id = addr.scope_id();
            }

            mem::size_of::<sockaddr_in6>() as socklen_t
        };

        SockAddr { storage, len }
    }
}
impl From<SocketAddr> for SockAddr {
    fn from(value: SocketAddr) -> Self {
        match value {
            SocketAddr::V4(socket_addr_v4) => SockAddr::from(socket_addr_v4),
            SocketAddr::V6(socket_addr_v6) => SockAddr::from(socket_addr_v6),
        }
    }
}
impl SockAddr {
    pub const unsafe fn new(storage: SockAddrStorage, len: socklen_t) -> SockAddr {
        SockAddr {
            storage: storage.storage,
            len: len as socklen_t,
        }
    }
    pub unsafe fn set_length(&mut self, length: socklen_t) {
        self.len = length;
    }

    /// Returns this address's family.
    pub const fn family(&self) -> sa_family_t {
        self.storage.ss_family
    }

    /// Returns this address's `Domain`.
    pub const fn domain(&self) -> Domain {
        Domain(self.storage.ss_family as c_int)
    }

    /// Returns the size of this address in bytes.
    pub const fn len(&self) -> socklen_t {
        self.len
    }

    /// Returns a raw pointer to the address.
    pub const fn as_ptr(&self) -> *const SockAddrStorage {
        &self.storage as *const sockaddr_storage as *const SockAddrStorage
    }

    /// Retuns the address as the storage.
    pub const fn as_storage(self) -> SockAddrStorage {
        SockAddrStorage {
            storage: self.storage,
        }
    }

    /// Returns true if this address is in the `AF_INET` (IPv4) family, false otherwise.
    pub const fn is_ipv4(&self) -> bool {
        self.storage.ss_family == AF_INET as sa_family_t
    }

    /// Returns true if this address is in the `AF_INET6` (IPv6) family, false
    /// otherwise.
    pub const fn is_ipv6(&self) -> bool {
        self.storage.ss_family == AF_INET6 as sa_family_t
    }

    /// Returns true if this address is of a unix socket (for local interprocess communication),
    /// i.e. it is from the `AF_UNIX` family, false otherwise.
    pub fn is_unix(&self) -> bool {
        false
    }

    /// Returns this address as a `SocketAddr` if it is in the `AF_INET` (IPv4)
    /// or `AF_INET6` (IPv6) family, otherwise returns `None`.
    pub fn as_socket(&self) -> Option<SocketAddr> {
        if self.storage.ss_family == AF_INET as sa_family_t {
            // SAFETY: if the `ss_family` field is `AF_INET` then storage must
            // be a `sockaddr_in`.
            let addr = unsafe { &*(ptr::addr_of!(self.storage).cast::<sockaddr_in>()) };
            let ip = from_in_addr(addr.sin_addr);
            let port = u16::from_be(addr.sin_port);
            Some(SocketAddr::V4(SocketAddrV4::new(ip, port)))
        } else if self.storage.ss_family == AF_INET6 as sa_family_t {
            // SAFETY: if the `ss_family` field is `AF_INET6` then storage must
            // be a `sockaddr_in6`.
            let addr = unsafe { &*(ptr::addr_of!(self.storage).cast::<sockaddr_in6>()) };
            let ip = from_in6_addr(addr.sin6_addr);
            let port = u16::from_be(addr.sin6_port);
            Some(SocketAddr::V6(SocketAddrV6::new(
                ip,
                port,
                addr.sin6_flowinfo,
                addr.sin6_scope_id,
            )))
        } else {
            None
        }
    }

    /// Returns this address as a [`SocketAddrV4`] if it is in the `AF_INET`
    /// family.
    pub fn as_socket_ipv4(&self) -> Option<SocketAddrV4> {
        match self.as_socket() {
            Some(SocketAddr::V4(addr)) => Some(addr),
            _ => None,
        }
    }

    /// Returns this address as a [`SocketAddrV6`] if it is in the `AF_INET6`
    /// family.
    pub fn as_socket_ipv6(&self) -> Option<SocketAddrV6> {
        match self.as_socket() {
            Some(SocketAddr::V6(addr)) => Some(addr),
            _ => None,
        }
    }

    /// Returns the initialised storage bytes.
    fn as_bytes(&self) -> &[u8] {
        // SAFETY: `self.storage` is a C struct which can always be treated a
        // slice of bytes. Furthermore, we ensure we don't read any unitialised
        // bytes by using `self.len`.
        unsafe { std::slice::from_raw_parts(self.as_ptr().cast(), self.len as usize) }
    }
    pub unsafe fn try_init<F, T>(init: F) -> std::io::Result<(T, SockAddr)>
    where
        F: FnOnce(*mut SockAddrStorage, *mut socklen_t) -> std::io::Result<T>,
    {
        const STORAGE_SIZE: socklen_t = size_of::<sockaddr_storage>() as socklen_t;
        // NOTE: `SockAddr::unix` depends on the storage being zeroed before
        // calling `init`.
        // NOTE: calling `recvfrom` with an empty buffer also depends on the
        // storage being zeroed before calling `init` as the OS might not
        // initialise it.
        let mut storage = SockAddrStorage::zeroed();
        let mut len = STORAGE_SIZE;
        init(&mut storage, &mut len).map(|res| {
            debug_assert!(len <= STORAGE_SIZE, "overflown address storage");
            (res, unsafe { SockAddr::new(storage, len) })
        })
    }
}

impl std::fmt::Debug for SockAddr {
    fn fmt(&self, fmt: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        let mut f = fmt.debug_struct("SockAddr");
        #[cfg(any(
            target_os = "dragonfly",
            target_os = "freebsd",
            target_os = "haiku",
            target_os = "hermit",
            target_os = "ios",
            target_os = "visionos",
            target_os = "macos",
            target_os = "netbsd",
            target_os = "nto",
            target_os = "openbsd",
            target_os = "tvos",
            target_os = "vxworks",
            target_os = "watchos",
        ))]
        f.field("ss_len", &self.storage.ss_len);
        f.field("ss_family", &self.storage.ss_family)
            .field("len", &self.len)
            .finish()
    }
}

#[cfg(test)]
mod tests {
    use std::hash::Hash;

    use super::*;

    #[test]
    fn ipv4() {
        use std::net::Ipv4Addr;
        let std = SocketAddrV4::new(Ipv4Addr::new(1, 2, 3, 4), 9876);
        let addr = SockAddr::from(std);
        assert!(addr.is_ipv4());
        assert!(!addr.is_ipv6());
        assert!(!addr.is_unix());
        assert_eq!(addr.family(), AF_INET as sa_family_t);
        assert_eq!(addr.domain(), Domain::IPV4);
        assert_eq!(addr.len(), size_of::<sockaddr_in>() as socklen_t);
        assert_eq!(addr.as_socket(), Some(SocketAddr::V4(std)));
        assert_eq!(addr.as_socket_ipv4(), Some(std));
        assert!(addr.as_socket_ipv6().is_none());

        let addr = SockAddr::from(SocketAddr::from(std));
        assert_eq!(addr.family(), AF_INET as sa_family_t);
        assert_eq!(addr.len(), size_of::<sockaddr_in>() as socklen_t);
        assert_eq!(addr.as_socket(), Some(SocketAddr::V4(std)));
        assert_eq!(addr.as_socket_ipv4(), Some(std));
        assert!(addr.as_socket_ipv6().is_none());
        /*#[cfg(unix)]
        {
            assert!(addr.as_pathname().is_none());
            assert!(addr.as_abstract_namespace().is_none());
        }*/
    }

    #[test]
    fn ipv6() {
        use std::net::Ipv6Addr;
        let std = SocketAddrV6::new(Ipv6Addr::new(1, 2, 3, 4, 5, 6, 7, 8), 9876, 11, 12);
        let addr = SockAddr::from(std);
        assert!(addr.is_ipv6());
        assert!(!addr.is_ipv4());
        assert!(!addr.is_unix());
        assert_eq!(addr.family(), AF_INET6 as sa_family_t);
        assert_eq!(addr.domain(), Domain::IPV6);
        assert_eq!(addr.len(), size_of::<sockaddr_in6>() as socklen_t);
        assert_eq!(addr.as_socket(), Some(SocketAddr::V6(std)));
        assert!(addr.as_socket_ipv4().is_none());
        assert_eq!(addr.as_socket_ipv6(), Some(std));

        let addr = SockAddr::from(SocketAddr::from(std));
        assert_eq!(addr.family(), AF_INET6 as sa_family_t);
        assert_eq!(addr.len(), size_of::<sockaddr_in6>() as socklen_t);
        assert_eq!(addr.as_socket(), Some(SocketAddr::V6(std)));
        assert!(addr.as_socket_ipv4().is_none());
        assert_eq!(addr.as_socket_ipv6(), Some(std));
        /*#[cfg(unix)]
        {
            assert!(addr.as_pathname().is_none());
            assert!(addr.as_abstract_namespace().is_none());
        }*/
    }

    #[test]
    fn ipv4_eq() {
        use std::net::Ipv4Addr;

        let std1 = SocketAddrV4::new(Ipv4Addr::new(1, 2, 3, 4), 9876);
        let std2 = SocketAddrV4::new(Ipv4Addr::new(5, 6, 7, 8), 8765);

        test_eq(
            SockAddr::from(std1),
            SockAddr::from(std1),
            SockAddr::from(std2),
        );
    }

    #[test]
    fn ipv4_hash() {
        use std::net::Ipv4Addr;

        let std1 = SocketAddrV4::new(Ipv4Addr::new(1, 2, 3, 4), 9876);
        let std2 = SocketAddrV4::new(Ipv4Addr::new(5, 6, 7, 8), 8765);

        test_hash(
            SockAddr::from(std1),
            SockAddr::from(std1),
            SockAddr::from(std2),
        );
    }

    #[test]
    fn ipv6_eq() {
        use std::net::Ipv6Addr;

        let std1 = SocketAddrV6::new(Ipv6Addr::new(1, 2, 3, 4, 5, 6, 7, 8), 9876, 11, 12);
        let std2 = SocketAddrV6::new(Ipv6Addr::new(3, 4, 5, 6, 7, 8, 9, 0), 7654, 13, 14);

        test_eq(
            SockAddr::from(std1),
            SockAddr::from(std1),
            SockAddr::from(std2),
        );
    }

    #[test]
    fn ipv6_hash() {
        use std::net::Ipv6Addr;

        let std1 = SocketAddrV6::new(Ipv6Addr::new(1, 2, 3, 4, 5, 6, 7, 8), 9876, 11, 12);
        let std2 = SocketAddrV6::new(Ipv6Addr::new(3, 4, 5, 6, 7, 8, 9, 0), 7654, 13, 14);

        test_hash(
            SockAddr::from(std1),
            SockAddr::from(std1),
            SockAddr::from(std2),
        );
    }

    #[test]
    fn ipv4_ipv6_eq() {
        use std::net::Ipv4Addr;
        use std::net::Ipv6Addr;

        let std1 = SocketAddrV4::new(Ipv4Addr::new(1, 2, 3, 4), 9876);
        let std2 = SocketAddrV6::new(Ipv6Addr::new(1, 2, 3, 4, 5, 6, 7, 8), 9876, 11, 12);

        test_eq(
            SockAddr::from(std1),
            SockAddr::from(std1),
            SockAddr::from(std2),
        );

        test_eq(
            SockAddr::from(std2),
            SockAddr::from(std2),
            SockAddr::from(std1),
        );
    }

    #[test]
    fn ipv4_ipv6_hash() {
        use std::net::Ipv4Addr;
        use std::net::Ipv6Addr;

        let std1 = SocketAddrV4::new(Ipv4Addr::new(1, 2, 3, 4), 9876);
        let std2 = SocketAddrV6::new(Ipv6Addr::new(1, 2, 3, 4, 5, 6, 7, 8), 9876, 11, 12);

        test_hash(
            SockAddr::from(std1),
            SockAddr::from(std1),
            SockAddr::from(std2),
        );

        test_hash(
            SockAddr::from(std2),
            SockAddr::from(std2),
            SockAddr::from(std1),
        );
    }

    #[allow(clippy::eq_op)] // allow a0 == a0 check
    fn test_eq(a0: SockAddr, a1: SockAddr, b: SockAddr) {
        assert!(a0 == a0);
        assert!(a0 == a1);
        assert!(a1 == a0);
        assert!(a0 != b);
        assert!(b != a0);
    }

    fn test_hash(a0: SockAddr, a1: SockAddr, b: SockAddr) {
        assert!(calculate_hash(&a0) == calculate_hash(&a0));
        assert!(calculate_hash(&a0) == calculate_hash(&a1));
        // technically unequal values can have the same hash, in this case x != z and both have different hashes
        assert!(calculate_hash(&a0) != calculate_hash(&b));
    }

    fn calculate_hash(x: &SockAddr) -> u64 {
        use std::collections::hash_map::DefaultHasher;
        use std::hash::Hasher;

        let mut hasher = DefaultHasher::new();
        x.hash(&mut hasher);
        hasher.finish()
    }
}
