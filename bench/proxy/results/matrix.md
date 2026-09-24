# Proxy differential matrix

Each cell is the count of corpus entries in that family that produced each disposition at that front. Reference is the strict RFC 9112 framer in `refparse.py`.


## nginx

| family | n | clean | reject | front_stricter | desync | fwd_reject |
|---|---|---|---|---|---|---|
| bare_eol | 6 | 0 | 1 | 0 | 0 | 5 |
| baseline | 6 | 6 | 0 | 0 | 0 | 0 |
| chunk | 8 | 3 | 4 | 0 | 0 | 1 |
| cl_bad | 13 | 2 | 8 | 3 | 0 | 0 |
| cl_sweep | 18 | 1 | 15 | 2 | 0 | 0 |
| cl_te | 5 | 0 | 5 | 0 | 0 | 0 |
| ctrl | 7 | 1 | 6 | 0 | 0 | 0 |
| ctrl_sweep | 66 | 1 | 63 | 0 | 0 | 2 |
| expect | 2 | 2 | 0 | 0 | 0 | 0 |
| host | 3 | 1 | 2 | 0 | 0 | 0 |
| keepalive | 2 | 2 | 0 | 0 | 0 | 0 |
| name | 5 | 0 | 4 | 0 | 0 | 1 |
| obs_fold | 3 | 0 | 3 | 0 | 0 | 0 |
| pipe_sweep | 6 | 4 | 1 | 0 | 0 | 1 |
| pipeline | 4 | 4 | 0 | 0 | 0 | 0 |
| smuggle | 3 | 1 | 2 | 0 | 0 | 0 |
| target | 11 | 2 | 4 | 2 | 0 | 3 |
| target_sweep | 13 | 9 | 0 | 4 | 0 | 0 |
| te_cl | 1 | 0 | 1 | 0 | 0 | 0 |
| te_sweep | 20 | 5 | 13 | 1 | 0 | 1 |
| te_te | 13 | 2 | 10 | 1 | 0 | 0 |
| upgrade | 4 | 3 | 0 | 0 | 0 | 1 |

### notable at nginx

Active smuggling (backend framed a request count the front did not answer, or the backend errored): **0**. The rest are leniency: the front accepted a stream the strict reference rejects but normalised it to a single clean request before forwarding.

- `bare_eol / bare lf request line`: **fwd_reject** -- normalized (backend saw 1 req); up_targets=['/']
- `bare_eol / bare lf all`: **fwd_reject** -- normalized (backend saw 1 req); up_targets=['/']
- `bare_eol / bare lf header`: **fwd_reject** -- normalized (backend saw 1 req); up_targets=['/']
- `bare_eol / bare lf then chunk`: **fwd_reject** -- normalized (backend saw 1 req); up_targets=['/']
- `bare_eol / lf lf terminator`: **fwd_reject** -- normalized (backend saw 1 req); up_targets=['/']
- `name / unicode in name`: **fwd_reject** -- normalized (backend saw 1 req); up_targets=['/']
- `target / double space in line`: **fwd_reject** -- normalized (backend saw 1 req); up_targets=['/']
- `target / missing version`: **fwd_reject** -- normalized (backend saw 1 req); up_targets=['/']
- `target / http 0.9 style`: **fwd_reject** -- normalized (backend saw 1 req); up_targets=['/']
- `chunk / chunk trailer smuggle`: **fwd_reject** -- normalized (backend saw 1 req); up_targets=['/']
- `upgrade / upgrade trailing bytes`: **fwd_reject** -- normalized (backend saw 1 req); up_targets=['/ws']
- `ctrl_sweep / value byte 0a`: **fwd_reject** -- normalized (backend saw 1 req); up_targets=['/']
- `ctrl_sweep / target byte 0a`: **fwd_reject** -- normalized (backend saw 1 req); up_targets=['/a']
- `te_sweep / chunked cr`: **fwd_reject** -- normalized (backend saw 1 req); up_targets=['/']
- `pipe_sweep / good then bad`: **fwd_reject** -- normalized (backend saw 1 req); up_targets=['/a']

## haproxy

| family | n | clean | reject | front_stricter | desync | fwd_reject |
|---|---|---|---|---|---|---|
| bare_eol | 6 | 0 | 2 | 0 | 0 | 4 |
| baseline | 6 | 6 | 0 | 0 | 0 | 0 |
| chunk | 8 | 3 | 5 | 0 | 0 | 0 |
| cl_bad | 13 | 5 | 8 | 0 | 0 | 0 |
| cl_sweep | 18 | 3 | 15 | 0 | 0 | 0 |
| cl_te | 5 | 0 | 0 | 0 | 0 | 5 |
| ctrl | 7 | 1 | 6 | 0 | 0 | 0 |
| ctrl_sweep | 66 | 1 | 65 | 0 | 0 | 0 |
| expect | 2 | 2 | 0 | 0 | 0 | 0 |
| host | 3 | 1 | 2 | 0 | 0 | 0 |
| keepalive | 2 | 2 | 0 | 0 | 0 | 0 |
| name | 5 | 0 | 5 | 0 | 0 | 0 |
| obs_fold | 3 | 0 | 1 | 0 | 0 | 2 |
| pipe_sweep | 6 | 4 | 1 | 0 | 0 | 1 |
| pipeline | 4 | 4 | 0 | 0 | 0 | 0 |
| smuggle | 3 | 1 | 2 | 0 | 0 | 0 |
| target | 11 | 3 | 5 | 1 | 0 | 2 |
| target_sweep | 13 | 11 | 0 | 2 | 0 | 0 |
| te_cl | 1 | 0 | 1 | 0 | 0 | 0 |
| te_sweep | 20 | 6 | 14 | 0 | 0 | 0 |
| te_te | 13 | 3 | 10 | 0 | 0 | 0 |
| upgrade | 4 | 1 | 1 | 2 | 0 | 0 |

### notable at haproxy

Active smuggling (backend framed a request count the front did not answer, or the backend errored): **0**. The rest are leniency: the front accepted a stream the strict reference rejects but normalised it to a single clean request before forwarding.

- `cl_te / cl then te plain`: **fwd_reject** -- normalized (backend saw 1 req); up_targets=['/']
- `cl_te / cl then te upper`: **fwd_reject** -- normalized (backend saw 1 req); up_targets=['/']
- `cl_te / cl then te mixed`: **fwd_reject** -- normalized (backend saw 1 req); up_targets=['/']
- `cl_te / te then cl`: **fwd_reject** -- normalized (backend saw 1 req); up_targets=['/']
- `cl_te / cl zero te chunked`: **fwd_reject** -- normalized (backend saw 1 req); up_targets=['/']
- `obs_fold / folded value space`: **fwd_reject** -- normalized (backend saw 1 req); up_targets=['/']
- `obs_fold / folded value tab`: **fwd_reject** -- normalized (backend saw 1 req); up_targets=['/']
- `bare_eol / bare lf request line`: **fwd_reject** -- normalized (backend saw 1 req); up_targets=['/']
- `bare_eol / bare lf all`: **fwd_reject** -- normalized (backend saw 1 req); up_targets=['/']
- `bare_eol / bare lf header`: **fwd_reject** -- normalized (backend saw 1 req); up_targets=['/']
- `bare_eol / lf lf terminator`: **fwd_reject** -- normalized (backend saw 1 req); up_targets=['/']
- `target / double space in line`: **fwd_reject** -- normalized (backend saw 1 req); up_targets=['/']
- `target / bad version`: **fwd_reject** -- normalized (backend saw 1 req); up_targets=['/']
- `pipe_sweep / good then bad`: **fwd_reject** -- normalized (backend saw 1 req); up_targets=['/a']

## bend_httpd

| family | n | match_accept | match_reject | httpd_stricter | httpd_looser |
|---|---|---|---|---|---|
| bare_eol | 6 | 0 | 6 | 0 | 0 |
| baseline | 6 | 6 | 0 | 0 | 0 |
| chunk | 8 | 3 | 5 | 0 | 0 |
| cl_bad | 13 | 4 | 8 | 1 | 0 |
| cl_sweep | 18 | 2 | 15 | 1 | 0 |
| cl_te | 5 | 0 | 5 | 0 | 0 |
| ctrl | 7 | 1 | 6 | 0 | 0 |
| ctrl_sweep | 66 | 1 | 65 | 0 | 0 |
| expect | 2 | 2 | 0 | 0 | 0 |
| host | 3 | 1 | 2 | 0 | 0 |
| keepalive | 2 | 2 | 0 | 0 | 0 |
| name | 5 | 0 | 5 | 0 | 0 |
| obs_fold | 3 | 0 | 3 | 0 | 0 |
| pipe_sweep | 6 | 4 | 2 | 0 | 0 |
| pipeline | 4 | 4 | 0 | 0 | 0 |
| smuggle | 3 | 1 | 2 | 0 | 0 |
| target | 11 | 4 | 6 | 0 | 1 |
| target_sweep | 13 | 13 | 0 | 0 | 0 |
| te_cl | 1 | 0 | 1 | 0 | 0 |
| te_sweep | 20 | 4 | 14 | 2 | 0 |
| te_te | 13 | 2 | 10 | 1 | 0 |
| upgrade | 4 | 2 | 0 | 1 | 1 |

### notable at bend_httpd

- `target / very long header line`: **httpd_looser** accepted 1 (statuses [200]) for a reject stream
- `upgrade / upgrade trailing bytes`: **httpd_looser** accepted 1 (statuses [426]) for a reject stream
