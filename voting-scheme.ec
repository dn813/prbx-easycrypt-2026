require import AllCore List IntDiv Bool Distr.
require import Lrs.

(* Types *)
type cnd.  (* candidate *)
type vote.
type voter.
type cs = cnd list.  (* candidate selection *)
type ballot. (* encrypted vote *)
type bb = ballot list. (* bulletin board *)
type nizk. (* NIZK proof object *)
type result = vote list. (* final election result *)

type group = Lrs.G.group.
type exp = Lrs.exp.

(* Operations *)

(* Distributions *)


module type VS = {
  proc setup(ta_count: int): unit
  proc register(i: voter): pcred * scred
  proc setupelection(): ring * cs * event
  proc vote(cnd: cnd, sc_i: scred, i: voter): ballot
  proc isvalid(b: ballot, bb: bb): bool
  proc shuffle(bb: bb): nizk
  proc tally(sk: skey, bb: bb): result * nizk
  proc verify(bb: bb, t: result, pi: nizk): bool
}.

module type Adv = {
  proc coerce(vj: voter, cnd: cnd): unit
  proc guess(vj: voter): bool
}.

module type BB = {
  proc registerkey(pk: pkey, pk_ta: pkey): unit
}.

module VotingScheme : VS = {
  proc setup(ta_count: int): unit = {
    var params;
    var sk_ta: skey list <- [];
    var sk_ta_i: exp;
    var ta_i: int <- 0;
    params <@ LRS.setup();

    while (ta_i < ta_count) {
      sk_ta_i <$ dexp;
      sk_ta <- ta_sk ++ [sk_ta_i];
      ta_i <- ta_i + 1;
    }

    BB.registerkey();
  }
  
  proc setupelection(): ring * cs * event = {
    var ev: event;
    ev <- H_G();
  }

  proc register(i: voter): pc * sc = {
    return register(i);
  }
}.

module Adversary : Adv = {
  proc targetselect(): voter list = {
    var subset: voter list;
    return subset;
  }
  proc coerce(vj: voter, cnd: cnd, sc: sc): unit = {
    VotingScheme.vote(cnd, sc, vj);
  }
  proc guess(vj: voter): bool = {
    var guess: bool;
    guess <$ {0,1};
  }
}.

section games.



end section.
