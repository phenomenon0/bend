# The peers for the socket repros. Each mode prints one line that
# verify.sh matches.
#   peer.py echo PORT     send 01 80 fe 02, print the echo in hex
#   peer.py burst PORT N  open N connections at once, count the ones the
#                         server accepted within 1 s (SYN drops retry at 1 s)
#   peer.py hold PORT N   open N connections and hold them for 2 s
import socket
import sys
import time


def connect(port):
    for _ in range(400):
        try:
            return socket.create_connection(("127.0.0.1", port))
        except OSError:
            time.sleep(0.05)
    sys.exit("no server on " + str(port))


def echo(port):
    s = connect(port)
    s.sendall(b"\x01\x80\xfe\x02")
    s.settimeout(5)
    got = b""
    while True:
        d = s.recv(64)
        if not d:
            break
        got += d
    print(got.hex())


def burst(port, n):
    connect(port)  # waits for the listener; this one sits in the queue too
    socks = []
    for _ in range(n):
        s = socket.socket()
        s.setblocking(False)
        s.connect_ex(("127.0.0.1", port))
        socks.append(s)
    time.sleep(1.0)
    done = 1
    for s in socks:
        try:
            s.getpeername()
            done += 1
        except OSError:
            pass
    print("completed " + str(done) + " of " + str(n + 1))


def hold(port, n):
    socks = [connect(port)]
    for _ in range(n - 1):
        s = socket.socket()
        s.settimeout(0.2)
        try:
            s.connect(("127.0.0.1", port))
        except OSError:
            pass
        socks.append(s)
    time.sleep(2.0)
    print("held " + str(n))


if __name__ == "__main__":
    mode, port = sys.argv[1], int(sys.argv[2])
    if mode == "echo":
        echo(port)
    elif mode == "burst":
        burst(port, int(sys.argv[3]))
    elif mode == "hold":
        hold(port, int(sys.argv[3]))
