# The WebSocket client's errors (net/ws.bend's Ws.Err) as the HTTP
# client's (net/client.bend's NetError), for a program that speaks both
# and keeps one error type:
#
#   EUrl                     BadUrl
#   EDns                     Dns
#   EConnect 110/60          Timeout
#   EConnect 111/61          Refused
#   EConnect 13              Tls (the certificate refused)
#   EConnect, other          Io
#   ETime                    Timeout
#   EHead                    TooLarge
#   EHand                    Protocol (the handshake, and why)
#   ESend ERecv EEof EClosed Closed
#   EProto                   Protocol (the close code the connection failed with)
#   ERand                    Io
#   EPing                    Timeout (a server's keepalive went unanswered)
#
# (A ws:// or wss:// URL reads the same way through net/url.bend's
# parse.ws, which the HTTP client's parse shares.)
import Base
import ./ws.bend as Ws
import ./ws_hs.bend as H
import ./client.bend as Client

def of.connect(+c: U32) -> Client.NetError:
  Bool.pick(Client.NetError, U32.is_eq(c, 13), Client.Tls{"the certificate was refused"},
    Client.dial.err(c, "no connection"))

def of(e: Ws.Err) -> Client.NetError:
  match e:
    case Ws.EUrl{}:
      Client.BadUrl{"not a ws:// or wss:// URL"}
    case Ws.EDns{c}:
      Client.Dns{Bytes.append("the name did not resolve: ", U32.show(c))}
    case Ws.EConnect{+c}:
      of.connect(c)
    case Ws.ETime{}:
      Client.Timeout{}
    case Ws.EHead{}:
      Client.TooLarge{}
    case Ws.EHand{w}:
      Client.Protocol{Bytes.append("websocket handshake: ", H.hw.show(w))}
    case Ws.ESend{c}:
      Client.Closed{}
    case Ws.ERecv{c}:
      Client.Closed{}
    case Ws.EEof{}:
      Client.Closed{}
    case Ws.EProto{c}:
      Client.Protocol{Bytes.append("the websocket failed with ", U32.show(c))}
    case Ws.EClosed{}:
      Client.Closed{}
    case Ws.ERand{c}:
      Client.Io{c, "no random bytes"}
    case Ws.EPing{}:
      Client.Timeout{}
