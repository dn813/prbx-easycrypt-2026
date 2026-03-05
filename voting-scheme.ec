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
type exp = Lrs.GP.exp.

(* Operations *)
op ( * ): exp -> exp -> exp.
op ( - ): exp -> exp -> exp.
op ( ^ ): group -> exp -> group.
op reenc (pk: pkey, g: group) (c: group * group, r': exp) = (c .` 1 * g ^ r', c .` 2 * pk ^ r').

(* Distributions *)
op [uniform lossless full] dint: int distr.

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

module VotingScheme : VS = {
  var pk: pkey
  var g, h: generator
  var voter_pcreds: pcred list
  var ring_size: int
  
  proc setup(): unit = {
    var lrs_params;

    lrs_params <@ LRS.setup();

    g <- lrs_params .` 1;
    h <- lrs_params .` 2;
    pk <- lrs_params .` 5;
  }
  
  proc setupelection(): ring * cs * event = {
    ring_size <$ dint;
  }

  proc register(i: voter): pc * sc = {
    var creds: (pcred * scred);
    var pcred, pcred': pcred;
    var r';
    var pk_i: pkey;
    var sk_i: skey;
    
    (* Get credentials *)
    creds <@ LRS.kgen();
    pcred <- creds .` 1;
    sk_i <$ dexp;
    pk_i <- g ^ sk_i;

    (* Choose randomness - would be done by TA but we do it here, instead *)
    r' <$ exp;
    pcred' <- reenc(pk) (pcred, r');
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
