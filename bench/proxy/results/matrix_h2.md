# HTTP/2 downgrade vectors (nginx h2c front)

Replayed via the `h2` package with outbound validation off. `forwarded` is what the HTTP/1.1 upstream recorded after the downgrade.

| family | reject | clean | desync | fwd_reject |
|---|---|---|---|---|
| h2 | 0 | 2 | 0 | 0 |
| h2_cl | 2 | 0 | 0 | 0 |
| h2_crlf | 2 | 0 | 0 | 0 |
| h2_pseudo | 3 | 0 | 0 | 2 |
| h2_te | 0 | 0 | 0 | 1 |

## notable

A `fwd_reject` with `forwarded == 1` and no smuggled HTTP/1.1 request in the target means the front **sanitised** the vector: it dropped the forbidden header (transfer-encoding, connection) and forwarded a single clean length-delimited request. A `desync` would be an actual smuggled second request at the backend.

- `h2_te / transfer-encoding in h2`: **fwd_reject** up_targets=['/e'] body=[5]
- `h2_pseudo / pseudo after regular`: **fwd_reject** up_targets=['/'] body=[0]
- `h2_pseudo / connection header in h2`: **fwd_reject** up_targets=['/'] body=[0]
