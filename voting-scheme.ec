require import AllCore List Int Bool Distr.

(* Types *)
type pkey. (* public encryption key *)
type skey. (* private encryption key *)
type pcred. (* public credential *)
type scred. (* private credential *)
type rand. (* random for encryption *)
type gen. (* key generator *)
type secparam. (* security param *)
type voter = int. (* each voter is an index i in V_i *)
type cnd.  (* candidate *)
type vote.
type cs = cnd list.  (* candidate selection *)
type ring. (* LRS ring *)
type event.
type ballot. (* encrypted vote *)
type bb = ballot list. (* bulletin board *)
type nizk. (* NIZK proof object *)
type result = vote list. (* final election result *)

(* Operations *)
op setup: secparam -> pkey * pkey list * skey list.
op register: voter -> pcred * scred.

(* Distributions *)
op [lossless uniform full] drand: rand distr.


module GlobVar = {
  var bb: bb
  var elec_result: result
}.


module type VS = {
  proc setup(l: secparam): pk * pk_list * sk_list
  proc register(i: voter): pc * sc
  proc setupelection(): ring * cs * event
  proc vote(cnd: cnd, sc_i: sc, i: voter): ballot
  proc isvalid(b: ballot, bb: bb): bool
  proc shuffle(bb: bb): nizk
  proc tally(sk: sk, bb: bb): result * nizk
  proc verify(bb: bb, t: result, pi: nizk): bool
}.

module type Adv = {
  proc coerce(vj: voter, cnd: cnd): unit
  proc guess(vj: voter): bool
}.

module type BB = {
  proc registerkey(pk: pk, pk_ta: pk): unit
}.

module VotingScheme : VS = {
  proc setup(l: secparam): pk * pk_list * sk_list = {
    return setup(l);
  }

  proc register(i: voter): pc * sc = {
    return register(i);
  }

  proc setupelection(): ring * cs * event = {
    
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
