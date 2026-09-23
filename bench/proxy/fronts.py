"""Front definitions for the differential harness. A front is a thing that sits
in front of the echo-record upstream (a proxy) or answers directly (a server).
Each knows how to write its config and how to be started and stopped.

  nginx     one worker, proxy_pass to the upstream, upstream keep-alive on
  haproxy   one thread, a keep-alive (http-reuse always) backend
  bend_httpd  the Bend engine as a server, no upstream (direct-parse rival)
  proxyd    the Bend reverse proxy -- documented, launched when it lands

Ports live in 20400-20499. Configs and logs go to a caller-supplied work dir.
"""

import os
import shutil
import signal
import socket
import subprocess
import time


def wait_port(host, port, timeout=8.0):
    end = time.time() + timeout
    while time.time() < end:
        try:
            with socket.create_connection((host, port), 0.3):
                return True
        except OSError:
            time.sleep(0.05)
    return False


def _kill(proc):
    if proc is None:
        return
    try:
        proc.send_signal(signal.SIGTERM)
        proc.wait(timeout=4)
    except Exception:
        try:
            proc.kill()
        except Exception:
            pass


class Nginx:
    name = "nginx"
    is_proxy = True

    def __init__(self, work, front_port, upstream_port, pin_core=None):
        self.work = work
        self.front_port = front_port
        self.upstream_port = upstream_port
        self.pin_core = pin_core
        self.proc = None

    def _conf(self):
        d = os.path.join(self.work, "nginx")
        os.makedirs(os.path.join(d, "logs"), exist_ok=True)
        os.makedirs(os.path.join(d, "tmp"), exist_ok=True)
        conf = os.path.join(d, "nginx.conf")
        with open(conf, "w") as f:
            f.write("""\
worker_processes 1;
daemon off;
pid %(d)s/nginx.pid;
error_log %(d)s/logs/error.log warn;
events { worker_connections 1024; }
http {
  access_log off;
  client_body_temp_path %(d)s/tmp/body;
  proxy_temp_path %(d)s/tmp/proxy;
  fastcgi_temp_path %(d)s/tmp/fcgi;
  uwsgi_temp_path %(d)s/tmp/uwsgi;
  scgi_temp_path %(d)s/tmp/scgi;
  default_type application/octet-stream;
  upstream backend { server 127.0.0.1:%(up)d; keepalive 32; }
  server {
    listen 127.0.0.1:%(fr)d;
    location / {
      proxy_pass http://backend;
      proxy_http_version 1.1;
      proxy_set_header Connection "";
      proxy_read_timeout 3s;
      proxy_connect_timeout 2s;
    }
  }
}
""" % {"d": d, "up": self.upstream_port, "fr": self.front_port})
        return d, conf

    def start(self):
        d, conf = self._conf()
        cmd = ["nginx", "-p", d, "-c", conf]
        if self.pin_core is not None:
            cmd = ["taskset", "-c", str(self.pin_core)] + cmd
        self.proc = subprocess.Popen(cmd, stdout=subprocess.DEVNULL,
                                     stderr=subprocess.DEVNULL)
        return wait_port("127.0.0.1", self.front_port)

    def stop(self):
        _kill(self.proc)
        self.proc = None


class NginxH2:
    """nginx with a cleartext HTTP/2 (h2c, prior-knowledge) listener that
    proxies to the HTTP/1.1 upstream. Used to probe the h2->1.1 downgrade
    vectors: whether the front sanitises what it forwards."""
    name = "nginx_h2"
    is_proxy = True

    def __init__(self, work, front_port, upstream_port, pin_core=None):
        self.work = work
        self.front_port = front_port
        self.upstream_port = upstream_port
        self.pin_core = pin_core
        self.proc = None

    def _conf(self):
        d = os.path.join(self.work, "nginx_h2")
        os.makedirs(os.path.join(d, "logs"), exist_ok=True)
        os.makedirs(os.path.join(d, "tmp"), exist_ok=True)
        conf = os.path.join(d, "nginx.conf")
        with open(conf, "w") as f:
            f.write("""\
worker_processes 1;
daemon off;
pid %(d)s/nginx.pid;
error_log %(d)s/logs/error.log warn;
events { worker_connections 1024; }
http {
  access_log off;
  client_body_temp_path %(d)s/tmp/body;
  proxy_temp_path %(d)s/tmp/proxy;
  fastcgi_temp_path %(d)s/tmp/fcgi;
  uwsgi_temp_path %(d)s/tmp/uwsgi;
  scgi_temp_path %(d)s/tmp/scgi;
  default_type application/octet-stream;
  upstream backend { server 127.0.0.1:%(up)d; keepalive 32; }
  server {
    listen 127.0.0.1:%(fr)d http2;
    location / {
      proxy_pass http://backend;
      proxy_http_version 1.1;
      proxy_set_header Connection "";
      proxy_read_timeout 3s;
    }
  }
}
""" % {"d": d, "up": self.upstream_port, "fr": self.front_port})
        return d, conf

    def start(self):
        d, conf = self._conf()
        cmd = ["nginx", "-p", d, "-c", conf]
        if self.pin_core is not None:
            cmd = ["taskset", "-c", str(self.pin_core)] + cmd
        self.proc = subprocess.Popen(cmd, stdout=subprocess.DEVNULL,
                                     stderr=subprocess.DEVNULL)
        return wait_port("127.0.0.1", self.front_port)

    def stop(self):
        _kill(self.proc)
        self.proc = None


class HAProxy:
    name = "haproxy"
    is_proxy = True

    def __init__(self, work, front_port, upstream_port, pin_core=None):
        self.work = work
        self.front_port = front_port
        self.upstream_port = upstream_port
        self.pin_core = pin_core
        self.proc = None

    def _conf(self):
        d = os.path.join(self.work, "haproxy")
        os.makedirs(d, exist_ok=True)
        cfg = os.path.join(d, "haproxy.cfg")
        with open(cfg, "w") as f:
            f.write("""\
global
  nbthread 1
defaults
  mode http
  option http-keep-alive
  timeout connect 2s
  timeout client 5s
  timeout server 5s
frontend fe
  bind 127.0.0.1:%(fr)d
  default_backend be
backend be
  http-reuse always
  server s1 127.0.0.1:%(up)d
""" % {"fr": self.front_port, "up": self.upstream_port})
        return cfg

    def start(self):
        cfg = self._conf()
        cmd = ["haproxy", "-f", cfg, "-db"]
        if self.pin_core is not None:
            cmd = ["taskset", "-c", str(self.pin_core)] + cmd
        self.proc = subprocess.Popen(cmd, stdout=subprocess.DEVNULL,
                                     stderr=subprocess.DEVNULL)
        return wait_port("127.0.0.1", self.front_port)

    def stop(self):
        _kill(self.proc)
        self.proc = None


class BendHttpd:
    name = "bend_httpd"
    is_proxy = False   # a direct server: it frames the client bytes itself

    def __init__(self, work, front_port, binary, pin_core=None):
        self.work = work
        self.front_port = front_port
        self.binary = binary
        self.pin_core = pin_core
        self.proc = None

    def start(self):
        cmd = [self.binary, "--port", str(self.front_port), "--idle-ms", "3000"]
        if self.pin_core is not None:
            cmd = ["taskset", "-c", str(self.pin_core)] + cmd
        self.proc = subprocess.Popen(cmd, stdout=subprocess.DEVNULL,
                                     stderr=subprocess.DEVNULL)
        return wait_port("127.0.0.1", self.front_port)

    def stop(self):
        _kill(self.proc)
        self.proc = None
