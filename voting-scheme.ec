require import AllCore List Int Bool Distr.

type pk.
type sk.
type pk_list = pk list.
type sk_list = sk list.
type pc.
type sc.
type group.
type secparam.
type voter = int.
type cnd.
type votes = int distr.
type cs = cnd list.
type ring.
type event.
type ballot.
type bb.
type nizk.
type result = int list.

op setup: secparam -> pk * pk_list * sk_list.
op register: voter -> pc * sc.



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
    var pc:
     register(i);
  }

  proc setupelection()
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
    guess <$ [false..true];
  }
}.

section games.



end section.
