# Proxy performance

wrk against `/health`. Front on core 0, upstream (Bend httpd) on core 1, client on cores 2-3. `bend_httpd` is the httpd as a direct server (no proxy hop).

| front | conns | req/s | p50 ms | p99 ms | peak RSS KB |
|---|---|---|---|---|---|
| nginx | 32 | 24139 | 1.09 | 8.18 | 7116 |
| nginx | 256 | 19153 | 12.29 | 38.50 | 7116 |
| haproxy | 32 | 27840 | 0.71 | 9.38 | 16836 |
| haproxy | 256 | 33535 | 6.43 | 22.90 | 21392 |
| bend_httpd | 32 | 63387 | 0.42 | 5.71 | 8400 |
| bend_httpd | 256 | 67633 | 3.44 | 11.28 | 8400 |
