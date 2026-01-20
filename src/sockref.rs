use std::{fmt, marker::PhantomData, mem::ManuallyDrop, ops::Deref};

use crate::Socket;

pub struct SockRef<'s> {
    /// Because this is a reference we don't own the `Socket`, however `Socket`
    /// closes itself when dropped, so we use `ManuallyDrop` to prevent it from
    /// closing itself.
    socket: ManuallyDrop<Socket>,
    /// Because we don't own the socket we need to ensure the socket remains
    /// open while we have a "reference" to it, the lifetime `'s` ensures this.
    _lifetime: PhantomData<&'s Socket>,
}

impl<'s> Deref for SockRef<'s> {
    type Target = Socket;

    fn deref(&self) -> &Self::Target {
        &self.socket
    }
}

impl fmt::Debug for SockRef<'_> {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        f.debug_struct("SockRef")
            .field("raw", &self.socket.as_raw())
            .field("local_addr", &self.socket.local_addr().ok())
            .field("peer_addr", &self.socket.peer_addr().ok())
            .finish()
    }
}
/*pub impl<'s> SockRef<'s> {
    pub fn bind(&self, address: &SockAddr) -> Result<()>
    {todo!()}
    pub fn connect(&self, address: &SockAddr) -> Result<()>
    {todo!()}
    pub fn connect_timeout(&self, addr: &SockAddr, timeout: Duration) -> Result<()>
    {todo!()}
    pub fn listen(&self, backlog: c_int) -> Result<()>
    {todo!()}
    pub fn accept(&self) -> Result<(Socket, SockAddr)>
    {todo!()}
    pub fn accept_raw(&self) -> Result<(Socket, SockAddr)>
    {todo!()}
    pub fn local_addr(&self) -> Result<SockAddr>
    {todo!()}
    pub fn peer_addr(&self) -> Result<SockAddr>
    {todo!()}
    pub fn r#type(&self) -> Result<Type>
    {todo!()}
    pub fn try_clone(&self) -> Result<Socket>
    {todo!()}
    pub fn nonblocking(&self) -> Result<bool>
    //Available {todo!()} on crate feature all and Unix only.
    {todo!()}
    pub fn set_nonblocking(&self, nonblocking: bool) -> Result<()>
    {todo!()}
    pub fn shutdown(&self, how: Shutdown) -> Result<()>
    {todo!()}
    pub fn recv(&self, buf: &mut [MaybeUninit<u8>]) -> Result<usize>
    {todo!()}
    pub fn recv_out_of_band(&self, buf: &mut [MaybeUninit<u8>]) -> Result<usize>
    {todo!()}
    pub fn recv_with_flags(
        &self,
        buf: &mut [MaybeUninit<u8>],
        flags: c_int,
    ) -> Result<usize> {todo!()}
}*/
