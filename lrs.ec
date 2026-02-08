require import AllCore List Bool Ring IntDiv.
require (****) Group.

clone Group.CyclicGroup as G.

axiom prime_p : prime G.order.
  
clone G.PowZMod as GP with
  lemma prime_order <- prime_p.

import G GP.

theory LRSTypes.
  type pkey = group. (* public encryption key *)
  type skey = exp. (* private encryption key *)
  type pcred = group * group. (* public credential/signature *)
  type scred = exp * exp * exp. (* private credential/signature *)
  type sig. (* Signature *)
  type generator = group. (* Group generator *)
  type ring.

  type string.
  type event = string.
  type tag = group.

  type ptxt. (* Plaintext *)
  type ctxt. (* Ciphertext *)

  op encode_group: group -> string.
  op encode_exp: exp -> string.z
  op H_G: string -> group.
  op H_q: string -> exp.

  op [lossless uniform full] dgroup: group distr.
  op [lossless uniform full] dexp: exp distr.
  
  op enc (pk: pkey) (m: group, r: exp) = (g ^ r, m * (pk ^ r)). (* enc() *)
end LRSTypes.
export LRSTypes.  
  
module type LinkableRingSS = {
  proc setup(): generator * generator * (string -> group) * (string -> exp) * pkey
  proc kgen(): pcred * scred
  proc sign(L: pcred list, ev: event, sc: scred, m: group): sig
  proc verify(L: ring, ev: event, m: ptxt, s: sig): bool
  proc link(s1: sig, s2: sig): bool
}.

module LRS : LinkableRingSS = {
  var g, h: generator
  var pk: pkey
  proc setup(): generator * generator * (string -> group) * (string -> exp) * pkey = {
    var sk: skey;

    g <$ dgroup;
    h <$ dgroup;

    sk <$ dexp;
    pk <- g ^ sk;
    
    return (g, h, H_G, H_q, pk);
  }
  
  proc kgen(): pcred * scred = {
    var x, y, r: exp;
    var sc: scred;
    var pc: pcred;
    x <$ dexp;
    y <$ dexp;
    r <$ dexp;
    sc <- (x, y, r);

    pc <- enc(pk) (g ^ x * h ^ y) (r);
    return (pc, sc);
  }

  proc sign(L: pcred list, ev: event, sc_i: scred, m: group): sig = {
    var e: group;
    var t: tag;
    var xi, yi, ri;
    var alp, bet, gam, c;
    var ki, ki', ki'';

    xi <- sc_i .` 1;
    yi <- sc_i .` 2;
    ri <- sc_i .` 3;

    e <- H_G(ev);
    t <- e ^ xi;
    
    alp <$ dexp;
    bet <$ dexp;
    gam <$ dexp;

    ki <- g ^ alp * h ^ gam * pk ^ bet;
    ki' <- g ^ bet;
    ki'' <- e ^ alp;
    c <- H_q();
  }
}.
