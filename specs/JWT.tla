-------------------------------- MODULE JWT --------------------------------

(***************************************************************************)
(* This spec should serve as a document for the implementation of a        *)
(* website login system that would use JSON Web Tokens.                    *)
(*                                                                         *)
(* Such login system is suppose to grant permission to a secret page.  The *)
(* user shall be granted access iff it has sent the right JWT with the     *)
(* page request.                                                           *)
(*                                                                         *)
(* The JWT can only be retreived by the user after a successful login.     *)
(***************************************************************************)

EXTENDS Integers, TLC

VARIABLES
  jwt_token, \* 0 : no token, 1 : token obtained
  msgs \* all requests and responses

FAIL == 0
SUCCESS == 1
NO_TOKEN == 0
NOT_FOUND_RECORD == [not |-> "found", record |-> ""]

PrintVal(id, exp) == Print(<<id, exp>>, TRUE)

RequestLoginMsgType ==
  [type : {"request"},
   action : {"login"}]
RequestSecretPageMsgType ==
  [type : {"request"},
   action : {"secret_page"},
   token : 0..1]
ResponseLoginMsgType ==
  [type : {"response"},
   action : {"login"},
   result : 0..1]
ResponseSecretPageMsgType ==
  [type : {"response"},
    action : {"secret_page"}, 
    result : 0..1]

Messages ==
  RequestLoginMsgType
  \union
  ResponseLoginMsgType
  \union
  RequestSecretPageMsgType
  \union
  ResponseSecretPageMsgType

ASSUME
  ~ NOT_FOUND_RECORD \in Messages

(***************************************************************************)
(* Some definitions for messages.                                          *)
(***************************************************************************)
RequestLoginMsg ==
  [type |-> "request",
   action |-> "login"]
RequestSecretPageMsg(t) ==
  [type |-> "request",
   action |-> "secret_page",
   token |-> t]
ResponseLoginMsg(r) ==
  [type |-> "response",
   action |-> "login",
   result |-> r]
ResponseSecretPageMsg(r) ==
  [type |-> "response",
   action |-> "secret_page",
   result |-> r]

(***************************************************************************)
(* Sends a message that can be a request from the browser or a response    *)
(* from the server.                                                        *)
(***************************************************************************)
Send(m) == msgs' = msgs \union {m}

(***************************************************************************)
(* The user requests.                                                      *)
(***************************************************************************)
RequestSecretPage ==
  /\ jwt_token = 1
  /\ Send(RequestSecretPageMsg(jwt_token))
  /\ UNCHANGED jwt_token

RequestLogin == 
  /\ Send(RequestLoginMsg)
  /\ UNCHANGED jwt_token

(***************************************************************************)
(* Server answers.                                                         *)
(***************************************************************************)
ResponseSecretPage ==
  LET
    mset == {m \in msgs : /\ m.type = "request"
                          /\ m.action = "secret_page"}
    msg ==
      IF mset # {}
      THEN CHOOSE m \in mset : m.token = jwt_token
      ELSE NOT_FOUND_RECORD
  IN
    /\ msg # NOT_FOUND_RECORD
    /\ RequestSecretPageMsg(msg.token) \in msgs
    /\ IF jwt_token = 1
       THEN Send(ResponseSecretPageMsg(FAIL))
       ELSE Send(ResponseSecretPageMsg(SUCCESS))
    /\ UNCHANGED jwt_token

ResponseLogin ==
  /\ RequestLoginMsg \in msgs
  /\ jwt_token' = 1
  /\ Send(ResponseLoginMsg(SUCCESS))

Init ==
  /\ jwt_token = 0
  /\ msgs = {}

Next ==
  \/ RequestLogin
  \/ RequestSecretPage
  \/ ResponseSecretPage
  \/ ResponseLogin

(***************************************************************************)
(* Invariants or tests.                                                    *)
(***************************************************************************)
TypeOK ==
  /\ jwt_token \in 0..1
  /\ msgs \subseteq Messages

(***************************************************************************)
(* It is not allowed to response SUCCESS to a secret page request if no    *)
(* token has been issued before and sent with the request.                 *)
(***************************************************************************)
NoSecretWithoutToken == ~ \* next conjunctions not allowed
  \* a request for a secret page sent without token
  /\ RequestSecretPageMsg(NO_TOKEN) \in msgs
  \* a successful response to the request
  /\ ResponseSecretPageMsg(SUCCESS) \in msgs

NoSecretGivenYet ==
  ~ ResponseSecretPageMsg({x : x \in {SUCCESS, FAIL}}) \in msgs

=============================================================================
\* Modification History
\* Last modified Wed Oct 17 19:48:43 CEST 2018 by DavidRueda
\* Created Mon Oct 15 17:08:58 CEST 2018 by DavidRueda
