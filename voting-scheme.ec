require import AllCore List IntDiv Bool DBool Distr DList.
require import Lrs.

(* Types *)
type voter = int.
type bb. (* bulletin board *)
type ballot = ptxt * ring * sig. (* encrypted vote *)

type group = Lrs.G.group.
type exp = Lrs.GP.exp.

type cnd = group.  (* candidate *)

(* Operations *)
abbrev ( * ) = Lrs.G.( * ).
abbrev ( ^ ) = Lrs.GP.( ^ ).
op ( - ): exp -> exp -> exp.
op reenc (pk: pkey, g: group) (c: group * group, r': exp) = (c .` 1 * g ^ r', c .` 2 * pk ^ r'). (* ReEnc() *)
op get_ev: unit -> event.

(* Distributions *)
op [uniform lossless full] dint: int distr.
op dcnd: cnd distr.

module type VS = {
  proc setup(): unit
  proc register(i: voter): pcred * scred
  proc setupelection(): unit
  proc vote(cnd: cnd, sc_i: scred, i: voter): ballot
  proc getev(): event
}.

module VotingScheme : VS = {
  var pk: pkey
  var g, h: generator
  var l0: pcred list (* L^(0) - list of encrypted credentials *)
  var ring_size: int (* Global constant ring size β *)
  var ev: event

  proc getev(): event = {return ev;}
  
  proc setup(): unit = {
    var lrs_params;

    lrs_params <@ LRS.setup();

    (* Set generators and TA total public key *)
    g <- lrs_params .` 1;
    h <- lrs_params .` 2;
    pk <- lrs_params .` 5;
  }
  
  proc setupelection(): unit = {
    (* Set constant global ring size at random (β) *)
    ring_size <$ [1..size l0];
    ev <- get_ev();
  }

  proc register(i: voter): pcred * scred = {
    var creds: (pcred * scred);
    var pc, pc': pcred;
    var sc: scred;
    var r';
    var pk_i: pkey;
    var sk_i: skey;
    
    (* Get credentials *)
    creds <@ LRS.kgen();
    pc <- creds .` 1;
    sc <- creds .` 2;
    sk_i <$ dexp;
    pk_i <- g ^ sk_i;

    (* Choose randomness - would be done by RA but we do it here, instead *)
    r' <$ dexp;
    pc' <- reenc(pk) (g) (pc) (r');

    l0 <- l0 ++ [pc'];

    return (pc', sc);
  }

  proc vote(cnd: cnd, sc_i: scred, i: voter): ballot = {
    var r_i, r, r_j: exp; (* randomness for encryptions *)
    var x_i, y_i; (* elements of sc*_i *)
    var pc_i; (* public counterpart to sc*_i *)
    var j, li_j_index: int; (* index j, and index of j-th selection from L^(0) *)
    var li, l0_no_i: ring; (* list L^(i) and L^(0) without the i-th credential *)
    var li_j: pcred; (* j-th credential to be added to L^(i) *)
    var ith_insert_i; (* Index of where to insert pc*_i *)
    var m_i: ptxt; (* Encrypted ballot to be signed *)
    var sig_i: sig; (* Ballot signature *)
    var b_i: ballot; (* Ballot *)
    r_i <$ dexp;
    r <$ dexp;
    
    x_i <- sc_i .` 1; (* x*_i *)
    y_i <- sc_i .` 2; (* y*_i *)

    pc_i <- enc (pk) (g) (g ^ x_i * h ^ y_i) (r_i); (* pc*_i *)
    
    j <- 1;
    li_j <- pc_i; (* Initialise li_j to pc_i as it is available - will be overwritten *)
    l0_no_i <- drop i l0;
    li <- nseq (ring_size - 1) li_j; (* Initialise list L^(i) using pc_i/li_j *)
    while (j < ring_size) {
      r_j <$ dexp; (* Randomly select randomness for re-encrypting jth credential *)
      if (j <> i) {
        li_j_index <$ [1..size l0_no_i];  (* Is this the right way to do this? *)
        li_j <- nth li_j l0_no_i li_j_index;
        li_j <- reenc (pk) (g) (li_j) (r_j);

        (* insert j-th encrypted credentials into L^(i) *)
        li <- put li j li_j; 
      }
      j <- j + 1;
    }

    (* Insert pc*_i into a random position in L^(i) *)
    ith_insert_i <$ [1..ring_size];
    li <- insert pc_i li ith_insert_i;

    m_i <- enc (pk) (g) (cnd) (r);
    sig_i <@ LRS.sign(li, ev, sc_i, m_i);

    b_i <- (m_i, li, sig_i);
    return b_i;
  }
}.

module type Adv = {
  (* Pick a target for coercion attempt *)
  proc picktarget(): voter
  (* Cast a ballot using obtained credential *)
  proc vote(): ballot
  (* Guess whether the voter followed instructions *)
  proc guess(): bool
  (* Receive and store the potentially faked credential from voter *)
  proc receive(sc': scred): unit
}.

module Adversary : Adv = {
  var votersc': scred
  var choice: cnd
  var target: voter

  proc picktarget(): voter = {
    target <$ [1..size VotingScheme.l0];
    return target;
  }

  proc vote(): ballot = {
    var ballot;
    ballot <@ VotingScheme.vote(choice, votersc', target);
    return ballot;
  }
  proc guess(): bool = {
    var guess: bool;
    guess <$ {0,1};
    return guess;
  }

  proc receive(sc': scred): unit = {
    votersc' <- sc';
  }
}.

section Games.

local module type Voter = {
  (* Decide behaviour (cooperate or deceive) *)
  proc flip(): unit
  (* Register with RA to receive credentials *)
  proc register(voter: voter): unit
  (* Provide coercer with credentials - real or fake *)
  proc yieldsc(): scred
  (* Vote - if real credential not forfeited *)
  proc vote(): ballot
  (* Reveal voter behvaiour - inaccessible to Adv *)
  proc revealb(): bool
}.

local module Voter0 : Voter = {
  var behaviour: bool
  var sc: scred
  var voter: voter

  proc flip(): unit = {
    behaviour <$ {0,1};
  }

  proc register(voter: voter): unit = {
    var creds: pcred * scred;
    creds <@ VotingScheme.register(voter);
    sc <- creds .` 2;
    voter <- voter;
  }

  proc yieldsc(): scred = {
    var sc': scred;
    var kgen_creds: pcred * scred;
    if (behaviour = true) {
      (* Yield real credential *)
      sc' <- sc;
    }
    else {
      (* Generate fake credential *)
      kgen_creds <@ LRS.kgen();
      sc' <- kgen_creds .` 2;
    }
    return sc';
  }

  proc vote(): ballot = {
    var choice: cnd;
    var ballot: ballot;
    (* Vote using real credential in moment of privacy *)
    choice <$ dcnd;
    ballot <@ VotingScheme.vote(choice, sc, voter);
    return ballot;
  }

  proc revealb(): bool = {return behaviour;}
}.

local module Voter1 : Voter = {
  var behaviour: bool
  var sc: scred
  var voter: voter

  proc flip(): unit = {
    behaviour <$ {0,1};
  }

  proc register(voter: voter): unit = {
    var creds: pcred * scred;
    creds <@ VotingScheme.register(voter);
    sc <- creds .` 2;
    voter <- voter;
  }

  proc yieldsc(): scred = {
    var sc': scred;
    var kgen_creds: pcred * scred;
    if (behaviour = true) {
      (* Yield real credential *)
      sc' <- sc;
    }
    else {
      (* Generate fake credential *)
      kgen_creds <@ LRS.kgen();
      sc' <- kgen_creds .` 2;
    }
    return sc';
  }

  proc vote(): ballot = {
    var choice: cnd;
    var kgen_creds: pcred * scred;
    var ballot: ballot;
    choice <$ dcnd;
    kgen_creds <@ LRS.kgen();
    ballot <@ VotingScheme.vote(choice, kgen_creds .` 2, voter);
    return ballot;
  }

  proc revealb(): bool = {return behaviour;}
}.

local module Voter2 : Voter = {
  var behaviour: bool
  var sc: scred
  var voter: voter

  proc flip(): unit = {
    behaviour <$ {0,1};
  }

  proc register(voter: voter): unit = {
    var creds: pcred * scred;
    creds <@ VotingScheme.register(voter);
    sc <- creds .` 2;
    voter <- voter;
  }

  proc yieldsc(): scred = {
    return sc; (* Always yield real credential, regardless of behaviour *)
  }

  proc vote(): ballot = {
   var choice: cnd;
   var ballot: ballot;
   (* Vote using real credential in moment of privacy *)
   choice <$ dcnd;
   ballot <@ VotingScheme.vote(choice, sc, voter);
   return ballot;
  }

  proc revealb(): bool = {return behaviour;}
}.

local module Game(V: Voter) (A: Adv) (VS: VS) = {
  proc main(): bool = {
    var votersc': scred;
    var voter: voter;
    var voter_ballot: ballot;
    var voter_valid: bool;
    var ev: event;
    var b', b: bool;

    voter <@ A.picktarget();
    V.register(voter);
    V.flip();
    votersc' <@ V.yieldsc();
    A.receive(votersc');

    VS.setupelection();

    A.vote();
    voter_ballot <@ V.vote();

    ev <@ VS.getev();

    voter_valid <@ LRS.verify(voter_ballot .` 2, ev, voter_ballot .` 1, voter_ballot .` 3);

    b' <@ A.guess();
    b <@ V.revealb();

    return b = b';
  }
}.


local lemma Games01_indist &m:
  `|Pr[Game(Voter0, Adversary, VotingScheme).main() @ &m : res]
  - Pr[Game(Voter1, Adversary, VotingScheme).main() @ &m : res]| = 0%r.
proof.
  proc*.
qed.

end section Games.

