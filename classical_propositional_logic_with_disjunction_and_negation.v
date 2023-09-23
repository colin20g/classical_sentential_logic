(** This program compiles with COQ 8.9*)

(** This software is a course on propositional classical logic. The objects we study are
    (a priori not quantified) sentences, where the primary logical connectors are the 
    disjunction "or" and the negation "not". "A or B" intuitively means "at least one of 
    the sentences A and B is true" and "not A" means the contrary of A.
    "A implies B" is thus an abbreviation for "(not A) or B". 
    
    The text is made of two main parts (sections). The first one establishes the general 
    properties of a proof system which is defined immediately after this introduction and has 
    been invented by Bertrand Russell and Paul Bernays (it is a particular case 
    of what is called a "Hilbert system"; cf wikipedia for a survey of these). 
    We avoid the deduction theorem and instead build natural deduction procedures    
    that allow the code to be applied directly for instance to first order logic
    (we define "A_1, A_2... A_n |- B" as [(not A_1) or (not A_2) or ... or (not (A_n)) or B]
    and prove each introduction and elimination rule of Gentzen narutal deduction system 
    for every logical connector).    

     In the second part we study propositional calculus and introduce truth values,
     conjunctive and disjunctive normal forms of formulas, prove their equivalence 
     and from that we deduce the completeness theorem for propositional logic.
     
     NB: this work does not solve P vs NP and does not attempt to do it either.
     This highly difficult (still open at the date this text is written) problem is outside 
     the range of interests of the author, not to mention his abilities ...). 
     The complexities of programs featured in the second part are very poor (computing normal 
     forms etc) and we think it is pointless to try to improve them, their interest is 
     more theoretical.
 *)

Record Russell_Bernays_Proof_System:=
  make_rbps
    {
      RBPS_Sentence: Type;
      rbps_disjunction: RBPS_Sentence -> RBPS_Sentence -> RBPS_Sentence;
      rbps_negation: RBPS_Sentence -> RBPS_Sentence;
      RBPS_Theorem: RBPS_Sentence -> Type;
      rbps_axiom_scheme_1: forall x: RBPS_Sentence,
          RBPS_Theorem
            (rbps_disjunction (rbps_negation (rbps_disjunction x x)) x);
      rbps_axiom_scheme_2: forall x y: RBPS_Sentence,
          RBPS_Theorem
            (rbps_disjunction (rbps_negation x) (rbps_disjunction y x));
      rbps_axiom_scheme_3: forall x y: RBPS_Sentence,
          RBPS_Theorem (rbps_disjunction
                          (rbps_negation (rbps_disjunction x y)) (rbps_disjunction y x));
      rbps_axiom_scheme_4: forall x y z: RBPS_Sentence,
          RBPS_Theorem
            (rbps_disjunction
               (rbps_negation (rbps_disjunction (rbps_negation x) y))
               (rbps_disjunction (rbps_negation (rbps_disjunction z x)) (rbps_disjunction z y))
            );
      rbps_modus_ponens: forall x y: RBPS_Sentence,
          RBPS_Theorem (rbps_disjunction (rbps_negation x) y) -> RBPS_Theorem x ->
          RBPS_Theorem y      
    }.

(** The above is based on the following considerations: among the various sentences 
    that can be written in a certain formal system (for instance mathematics) there are 
    some of them called "theorems" (which means "provable in the system") intended to 
    be absolutely sure. 
    The only thing we claim to know about the aforementioned theorems is that:

    1°) given any sentences P,Q, whenever P and ((not P) or Q) (a.k.a. P implies Q) are both 
    theorems, then Q is also a theorem (this rule is usually called "modus-ponens").

    2°) given any sentences A,B,C, all of the following are theorems:
    (i) (A or A) implies A
    (ii) A implies (B or A)
    (iii) (A or B) implies (B or A)
    (iv) (A implies B) implies ((C or A) implies (C or B))
    
    The whole content of the first chapter below, although being rather large, 
    is entirely drawn from the rules 1°) and 2°) (i) (ii) (iii) (iv) and NOTHING ELSE!!! 
    In particular and although we stated that the intuitive intended meaning of "X or Y" was 
    "at least one of the sentences X,Y is true" (which helps understanding the rules above, 
    especially (i) and (ii) maybe, since in the everyday language "A or B" also implicitely 
    means that A and B are mutually exclusive, which is not the case in formal logic, math
    and in the present text), it turns out that we will never make any reference to 
    "truth" in the first chapter. It is important for the reader to realize that a proof 
    is something entirely of syntactic nature and that the content of the first part is 
    made of programs that build proofs upon other proofs or axiom schemes. 
    Truth values and the link between truth and proofs is explored only in the second part of 
    the text.
 *)

Section General_properties_of_the_Russell_and_Bernays_proof_system.

  Variable R: Russell_Bernays_Proof_System.
  
  Notation P:= (RBPS_Sentence R).

  Notation "|- a":= (RBPS_Theorem R a) (at level 45).
  Notation "a // b":= (rbps_disjunction R a b) (at level 43).
  Notation "! a":= (rbps_negation R a) (at level 41).
  Notation "a -o b":= (rbps_disjunction R (rbps_negation R a) b)
                        (right associativity, at level 44).
  Notation "a & b":=
    (rbps_negation R (rbps_disjunction R (rbps_negation R a) (rbps_negation R b)))
      (at level 42). 
  
  Ltac a1:= apply (rbps_axiom_scheme_1 R).
  Ltac a2:= apply (rbps_axiom_scheme_2 R).
  Ltac a3:= apply (rbps_axiom_scheme_3 R).
  Ltac a4:= apply (rbps_axiom_scheme_4 R).
  Ltac ap:= assumption.

  Ltac mp t := apply (rbps_modus_ponens R) with (x:= t).

  Definition rbps_syllogism (x y z:P): |- x -o y -> |- y -o z -> |- x -o z.
  Proof.
    intros A B. mp (x -o y). mp (y -o z). a4. ap. ap.
  Defined.

  Ltac syl t := apply rbps_syllogism with (y:= t).
  
  Definition rbps_identity (x:P): |- x -o x.
  Proof.
    syl (x // x). a2. a1.
  Defined.

  Ltac ai:= apply rbps_identity.
  
  Definition rbps_right_polarity (x y z:P): |- x -o y -> |- (z // x) -o (z // y).
  Proof.
    intro A; mp (x -o y). a4. assumption.
  Defined.

  Ltac pr:= apply rbps_right_polarity. 
 
  Definition rbps_left_polarity (x y z:P): |- x -o y -> |- (x // z) -o (y // z).
  Proof.
    intro A; syl (z // x). a3. syl (z // y). mp (x -o y). a4. ap. a3.
  Defined.

  Ltac pl:= apply rbps_left_polarity. 
  
  Definition rbps_permutation (x y:P): |- x // y -> |- y // x.
  Proof.
    intro A. mp (x // y). a3. ap.
  Defined.    

  Ltac per:= apply rbps_permutation.
  
  Definition rbps_double_negation_introduction (x:P): |- x -o (!! x).
  Proof.
    per. ai.
  Defined.

  Ltac dni:= apply rbps_double_negation_introduction.

  Definition rbps_negation_polarity (x y:P): |- x -o y -> |- (! y) -o (! x).
  Proof.
    intro A. mp (x -o (!! y)). a3. syl y. ap. dni.
  Defined.
  
  Ltac np:= apply rbps_negation_polarity.

  Definition rbps_double_negation_elimination (x : P): |- (! ! x) -o x.
  Proof.
    per. mp (x // (!x)). pr; dni. per; ai.
  Defined.

  Ltac dne:= apply rbps_double_negation_elimination.
  
  Definition rbps_or_left_intro (x y:P): |- x -o (x // y).
  Proof.
    syl (y // x). a2. a3.
  Defined.

  Ltac li:= apply rbps_or_left_intro.
  
  Definition rbps_double_polarity (x x' y y':P):
  |- x -o x' -> |- y -o y' -> |- (x // y) -o (x' // y').
  Proof.
    intros A B. syl (x // y'). pr; ap. pl; ap.
  Defined.

  Ltac dp:= apply rbps_double_polarity.

  Definition rbps_or_elim (x y z:P): |- x -o z -> |- y -o z -> |- (x // y) -o z.
  Proof.
    intros A B. syl (z // z). dp; assumption. a1.
  Defined.

  Ltac oe:= apply rbps_or_elim.

  Definition rbps_or_left_associativity (x y z:P): |- (x // (y // z)) -o ((x // y) // z).
  Proof.
    oe. syl (x // y). li. li. oe. syl (x // y). a2. li. a2.
  Defined.

  Ltac la:= apply rbps_or_left_associativity.

  Definition rbps_or_right_associativity (x y z:P): |- ((x // y) // z) -o (x // (y // z)).
  Proof.
    oe. oe. li. syl (y // z). li. a2. syl (y // z). a2. a2.
  Defined.

  Ltac ra:= apply rbps_or_right_associativity.

  (** Hilbert proof systems like the one we're manipulating are often very impractical;
   we introduce below the natural deduction invented by Gerhard Gentzen, which
   is more intuitive to use. *)

  Fixpoint rbps_sequent_left_formula (l: list P) (rightmost_term:P) {struct l}: P:=
    match l with
    | nil => ! rightmost_term 
    | cons h t => (rbps_sequent_left_formula t h) // (! rightmost_term) 
    end.
  
  (** Natural deduction consists actually in proving "Horn clauses". *)

  Definition rbps_sequent (G: list P) (f:P):=
    match G with
    |nil => f
    |cons h t => (rbps_sequent_left_formula t h) // f
    end.

  Notation "G /- f":= (RBPS_Theorem R (rbps_sequent G f)) (at level 46).

  Definition rbps_natural_deduction_logic (G: list P) (x:P): |- x -> G /- x.
  Proof.
    destruct G. simpl; intro; ap. simpl; intro; mp x. a2. ap.
  Defined.
    
  Definition rbps_natural_deduction_contraction (G: list P) (h x:P):
    cons h (cons h G) /- x -> cons h G /- x.
  Proof.
    intros A. destruct G. simpl; simpl in A. mp ((h -o ! h) // x). pl. a1. ap.
    mp (rbps_sequent (h :: (h :: r :: G)%list) x).  simpl; simpl in A. pl. oe. ai. a2. ap.
  Defined.

  Definition rbps_natural_deduction_weakening (G: list P) (h x:P): G /- x -> cons h G /- x.
  Proof.
    destruct G. simpl; intro A. mp x. a2. ap. simpl. intro A.
    mp (rbps_sequent_left_formula G r // x). pl. li. ap.
  Defined.

  Definition rbps_natural_deduction_head_axiom (G: list P) (h:P): cons h G /- h.
  Proof.
    destruct G. simpl; ai. simpl. mp (h -o h). pl. a2. ai.
  Defined.

  Definition rbps_natural_deduction_implies_intro (G: list P) (x y: P):
    cons x G /- y -> G /- (x -o y).
  Proof.
    destruct G. simpl; intro A. ap. simpl. intro A.
    mp ((rbps_sequent_left_formula G r // !x) // y). ra. ap.
  Defined.
    
  Definition rbps_s_property (x y z:P): |- x // (y -o z) -> |- x // y -> |- x // z.
  Proof.
    intros A B. mp (x // y). mp (x // (y -o z)). oe. syl (x // z). li. a2. a4. ap. ap.
  Defined.

  Definition rbps_natural_deduction_implies_elim (G: list P) (x y: P):
    G /- (x -o y) -> G /- x -> G /- y.  
  Proof.
    destruct G. simpl; intro A. mp x; ap. simpl; intro A. apply rbps_s_property; ap.
  Defined.

  Definition rbps_natural_deduction_or_left_intro (G: list P) (x y:P): G /- x -> G /- x // y.
  Proof.
    destruct G; simpl; intro A. mp (y // x). a3. mp x. a2. ap.
    mp (rbps_sequent_left_formula G r // (y // x)). pr. a3.
    mp (rbps_sequent_left_formula G r // x). mp (x -o (y // x)). a4. a2. ap.
  Defined.    

  Definition rbps_natural_deduction_or_right_intro (G: list P) (x y:P): G /- x -> G /- y // x.
  Proof.
    destruct G; simpl; intro A. mp x. a2. ap.
    mp (rbps_sequent_left_formula G r // x). mp (x -o (y // x)). a4. a2. ap.
  Defined.    

  Definition rbps_natural_deduction_or_elim (G: list P) (x y z:P):
    cons x G /- z -> cons y G /- z -> G /- x // y -> G /- z.
  Proof.
    destruct G. simpl; intros A B C. mp (z // z). a1. mp (x // y). dp; ap. ap.
    simpl. intros A B C. mp (rbps_sequent_left_formula G r // (x // y)).
    oe. li. oe. mp ((x -o rbps_sequent_left_formula G r) // z). ra.
    mp ((rbps_sequent_left_formula G r // ! x) // z). pl. a3. ap.
    mp ((y -o rbps_sequent_left_formula G r) // z). ra.
    mp ((rbps_sequent_left_formula G r // ! y) // z). pl. a3. ap. ap.
  Defined.
    
  Definition rbps_excluded_middle (x y:P): |- x // y -> |- (!x) // y -> |- y.
  Proof.
    intros A B. mp (x // y). oe. ap. ai. ap.
  Defined.

  Ltac em t:= apply rbps_excluded_middle with (x:= t).
  
  Definition rbps_explosion (x y:P): |- (!x) -o (x -o y).
  Proof.
    mp ((!x -o !x) // y). ra. mp (!x -o !x). li. ai.
  Defined.    
  
  Definition rbps_explosion_2 (x y:P): |- x -o (!x -o y).
  Proof.
    mp ((x -o !!x) // y). ra. mp (x -o !!x). li. dni.
  Defined.

  Definition rbps_explosion_3 (g x:P): |- g // x -> |- g // (! x) -> |- g.
  Proof.
    intros A B. mp (g // x). oe. ai. per; ap. ap.
  Defined.

  Definition rbps_explosion_4 (g x y:P): |- g // x -> |- g // (! x) -> |- g // y.
  Proof.
    intros A B. mp g. li. apply rbps_explosion_3 with (x:= x); ap.
  Defined.

  Definition rbps_natural_deduction_negation_elim (G: list P) (x y:P):
    G /- x -> G /- !x -> G /- y.
  Proof.
    destruct G. simpl; intros A B. em x. mp x. li. ap. mp (!x). li. ap.
    apply rbps_explosion_4.
  Defined.

  Definition rbps_natural_deduction_negation_intro (G: list P) (x y:P):
    cons x G /- y -> cons x G /- !y -> G /- !x.
  Proof.
    destruct G; simpl; intros A B; apply rbps_explosion_3 with (x:= y); ap.
  Defined.

  Definition rbps_natural_deduction_reductio_ad_absurdum (G: list P) (x y:P):
    cons (!x) G /- y -> cons (!x) G /- !y -> G /- x.
  Proof.
    destruct G. simpl; intros A B. mp (!! x). dne.
    apply (rbps_natural_deduction_negation_intro nil (! x) y); ap. intros A B.
    mp (rbps_sequent_left_formula G r // (!!x)). pr; dne. 
    apply (rbps_natural_deduction_negation_intro (cons r G) (! x) y A B).       
  Defined.

  Definition rbps_and_left_elim (x y:P): |- (x & y) -o x.
  Proof.
    syl (!! x). np. li. dne.
  Defined.

  Definition rbps_and_right_elim (x y:P): |- (x & y) -o y.
  Proof.
    syl (!! y). np. a2. dne.
  Defined.

  Definition rbps_and_intro_0 (x y:P): |- x -o (y -o x & y).
  Proof.
    mp ((x -o ! y) // (x & y)). ra. per; ai.
  Defined.
    
  Definition rbps_and_intro_1 (x y:P): |- x -> |- y -o (x & y).
  Proof.
    intro A. per. oe. mp (!! x). li. mp x. dni. ap. ai.
  Defined.
  
  Definition rbps_and_intro_2 (x y:P): |- x -> |- y -> |- x & y.
  Proof.
    intros A B. mp y. per. oe. mp x. apply rbps_explosion_2. ap. ai. ap.
  Defined.

  Definition rbps_and_intro_3 (g x y:P): |- g // x -> |- g // y -> |- g // (x & y).
  Proof.
    intros A B. mp (g // y). mp (g // x). oe. mp (g -o (g // (x & y))). pr. a2. li.
    syl (y -o (x & y)). apply rbps_and_intro_0. a4. ap. ap.
  Defined.

  Definition rbps_natural_deduction_and_intro (G: list P) (x y:P):
    G /- x -> G /- y -> G /- (x & y).
  Proof.
    destruct G. simpl; apply rbps_and_intro_2. simpl; apply rbps_and_intro_3.
  Defined.

  Definition rbps_natural_deduction_and_left_elim (G: list P) (x y:P):
    G /- x & y -> G /- x.
  Proof.
    destruct G. simpl. intro A; mp (x & y). apply rbps_and_left_elim. ap. simpl.
    intro A. mp (rbps_sequent_left_formula G r // x & y). pr; apply rbps_and_left_elim. ap.   
  Defined.

  Definition rbps_natural_deduction_and_right_elim (G: list P) (x y:P):
    G /- x & y -> G /- y.
  Proof.
    destruct G. simpl. intro A; mp (x & y). apply rbps_and_right_elim. ap. simpl.
    intro A. mp (rbps_sequent_left_formula G r // x & y). pr; apply rbps_and_right_elim. ap. 
  Defined.
  
  Section De_Morgan_and_distributivity_laws.

    Definition rbps_de_morgan_or (x y:P):
      prod (|- (! (x & y) -o (! x // ! y))) (|- ((! x // ! y) -o ! (x & y))).
    Proof.
      split. dne. dni.
    Defined.

    Definition rbps_de_morgan_and (x y:P):
      prod (|- (! (x // y) -o (! x & ! y))) (|- ((! x & ! y) -o ! (x // y))).
    Proof.
      split. np. dp; dne.  np. dp; dni.
    Defined.    

    Definition rbps_or_distributivity_over_and (x y z:P):
      prod (|- (x // (y & z)) -o ((x // y) & (x // z)))
           (|- ((x // y) & (x // z)) -o (x // (y & z))).
    Proof.
      split. oe. apply rbps_and_intro_3; simpl; li. apply rbps_and_intro_3. syl y.
      apply rbps_and_left_elim. a2. syl z. apply rbps_and_right_elim. a2.
      mp ((! (x // y) // ! (x // z)) // (x // y & z)). pl. dni.
      mp ((x // y) -o (x // z) -o (x // (y & z))). la. syl (x // (z -o (y & z))).
      pr. apply rbps_and_intro_0. oe. syl (x // (y & z)). li. a2. a4.
    Defined.     
      
    Definition rbps_and_distributivity_over_or (x y z:P):
      prod (|- (x & (y // z)) -o ((x & y) // (x & z)))
           (|- ((x & y) // (x & z)) -o (x & (y // z))).
    Proof.
      split. apply (rbps_natural_deduction_implies_intro (cons (x & (y // z)) nil)).
      apply rbps_natural_deduction_and_intro. apply rbps_natural_deduction_weakening.
      simpl; apply rbps_and_left_elim.
      apply rbps_natural_deduction_or_elim with (x:= y) (y:= z).
      apply rbps_natural_deduction_reductio_ad_absurdum with (y:= y).
      apply rbps_natural_deduction_weakening; apply rbps_natural_deduction_head_axiom. 
      apply rbps_natural_deduction_implies_elim with (x:= x).  
      apply rbps_natural_deduction_weakening; apply rbps_natural_deduction_weakening;
        apply rbps_natural_deduction_head_axiom.
      apply rbps_natural_deduction_and_left_elim with (y:= (y // z)).
      apply rbps_natural_deduction_weakening; apply rbps_natural_deduction_weakening;
        apply rbps_natural_deduction_weakening; apply rbps_natural_deduction_head_axiom.
      apply rbps_natural_deduction_head_axiom. 
      apply rbps_natural_deduction_and_right_elim with (x:= x).
      apply rbps_natural_deduction_weakening; apply rbps_natural_deduction_head_axiom.
      apply rbps_natural_deduction_and_intro with (G:= cons ((x -o !y) -o (x & z)) nil).
      apply rbps_natural_deduction_or_elim with (x := x & y) (y := x & z).
      apply rbps_natural_deduction_and_left_elim with (y:= y);
        apply rbps_natural_deduction_head_axiom. 
      apply rbps_natural_deduction_and_left_elim with (y:= z);
        apply rbps_natural_deduction_head_axiom. 
      apply rbps_natural_deduction_head_axiom. 
      apply rbps_natural_deduction_or_elim with (x := x & y) (y := x & z).
      apply rbps_natural_deduction_or_left_intro;
        apply rbps_natural_deduction_and_right_elim with (x:= x);
        apply rbps_natural_deduction_head_axiom.
      apply rbps_natural_deduction_or_right_intro;
        apply rbps_natural_deduction_and_right_elim with (x:= x);
        apply rbps_natural_deduction_head_axiom. 
      apply rbps_natural_deduction_head_axiom.
    Defined.
      
  End De_Morgan_and_distributivity_laws.  

  Section Equivalence_in_natural_deduction.

    Section Introduction_and_elimination_rules.

      Variable G: list P.      
      Variable x y: P.

      Definition rbps_natural_deduction_equivalence_intro: cons x G /- y -> cons y G /- x ->
                                                           G /- (x -o y) & (y -o x).
      Proof.
        intros A B; apply rbps_natural_deduction_and_intro;
          apply rbps_natural_deduction_implies_intro; ap.
      Defined.

      Definition rbps_natural_deduction_equivalence_left_right_elim:
        G /- (x -o y) & (y -o x) -> G /- x -> G /- y.
      Proof.
        intros A B. apply rbps_natural_deduction_implies_elim with (x := x).
        apply rbps_natural_deduction_and_left_elim with (y:= y -o x); ap. ap.
      Defined.                                                             

      Definition rbps_natural_deduction_equivalence_right_left_elim:
        G /- (x -o y) & (y -o x) -> G /- y -> G /- x.
      Proof.
        intros A B. apply rbps_natural_deduction_implies_elim with (x := y).
        apply rbps_natural_deduction_and_right_elim with (x:= x -o y); ap. ap.
      Defined.                                                         

    End Introduction_and_elimination_rules.

    Notation "p o-o q":= ((p -o q) & (q -o p)) (at level 43).
    
    Definition rbps_natural_deduction_equivalence_reflexivity (G: list P) (x:P):
      G /- x o-o x.
    Proof.
      apply rbps_natural_deduction_logic.  apply rbps_and_intro_2; ai.
    Defined.
    
    Definition rbps_natural_deduction_equivalence_symmetry (G: list P) (x y:P):
      G /- x o-o y -> G /- y o-o x.
    Proof.
      intro A. apply rbps_natural_deduction_and_intro.
      apply rbps_natural_deduction_and_right_elim with (x := x -o y); ap.
      apply rbps_natural_deduction_and_left_elim with (y := y -o x); ap.
    Defined.
    
    Definition rbps_natural_deduction_equivalence_transitivity (G: list P) (x y z:P):
      G /- x o-o y -> G /- y o-o z -> G /- x o-o z.
    Proof.
      intros A B. apply rbps_natural_deduction_equivalence_intro.
      apply rbps_natural_deduction_equivalence_left_right_elim with (x:= y).
      apply rbps_natural_deduction_weakening; ap.
      apply rbps_natural_deduction_equivalence_left_right_elim with (x:= x).
      apply rbps_natural_deduction_weakening; ap.
      apply rbps_natural_deduction_head_axiom.
      apply rbps_natural_deduction_equivalence_right_left_elim with (y:= y).
      apply rbps_natural_deduction_weakening; ap.
      apply rbps_natural_deduction_equivalence_right_left_elim with (y:= z).
      apply rbps_natural_deduction_weakening; ap.
      apply rbps_natural_deduction_head_axiom.
    Defined.

    Definition rbps_natural_deduction_equivalence_negation (G: list P) (x y:P):
      G /- x o-o y -> G /- (! x) o-o (! y).
    Proof.
      intro A. apply rbps_natural_deduction_equivalence_intro.
      apply rbps_natural_deduction_negation_intro with (y:= x).
      apply rbps_natural_deduction_equivalence_right_left_elim with (y := y).
      repeat apply rbps_natural_deduction_weakening; ap.
      apply rbps_natural_deduction_head_axiom.
      apply rbps_natural_deduction_weakening; apply rbps_natural_deduction_head_axiom.
      apply rbps_natural_deduction_negation_intro with (y:= y).
      apply rbps_natural_deduction_equivalence_left_right_elim with (x := x).
      repeat apply rbps_natural_deduction_weakening; ap.
      apply rbps_natural_deduction_head_axiom.
      apply rbps_natural_deduction_weakening; apply rbps_natural_deduction_head_axiom.
    Defined.

    Definition rbps_natural_deduction_equivalence_or (G: list P) (x x' y y':P):
      G /- x o-o x' -> G /- y o-o y' -> G /- (x // y) o-o (x' // y').
    Proof.
      intros A B. apply rbps_natural_deduction_equivalence_intro.
      apply rbps_natural_deduction_or_elim with (x:= x) (y:= y).
      apply rbps_natural_deduction_or_left_intro. 
      apply rbps_natural_deduction_equivalence_left_right_elim with (x:= x).
      repeat apply rbps_natural_deduction_weakening; ap.
      apply rbps_natural_deduction_head_axiom.
      apply rbps_natural_deduction_or_right_intro. 
      apply rbps_natural_deduction_equivalence_left_right_elim with (x:= y).
      repeat apply rbps_natural_deduction_weakening; ap.
      apply rbps_natural_deduction_head_axiom. apply rbps_natural_deduction_head_axiom.       
      apply rbps_natural_deduction_or_elim with (x:= x') (y:= y').
      apply rbps_natural_deduction_or_left_intro. 
      apply rbps_natural_deduction_equivalence_right_left_elim with (y:= x').
      repeat apply rbps_natural_deduction_weakening; ap.
      apply rbps_natural_deduction_head_axiom.
      apply rbps_natural_deduction_or_right_intro. 
      apply rbps_natural_deduction_equivalence_right_left_elim with (y:= y').
      repeat apply rbps_natural_deduction_weakening; ap.
      apply rbps_natural_deduction_head_axiom. apply rbps_natural_deduction_head_axiom. 
    Defined.     

    Definition rbps_natural_deduction_equivalence_implies (G: list P) (x x' y y':P):
      G /- x o-o x' -> G /- y o-o y' -> G /- (x -o y) o-o (x' -o y').
    Proof.
      intros A B; apply rbps_natural_deduction_equivalence_or.
      apply rbps_natural_deduction_equivalence_negation. ap. ap.
    Defined.

    Definition rbps_natural_deduction_equivalence_and (G: list P) (x x' y y':P):
      G /- x o-o x' -> G /- y o-o y' -> G /- (x & y) o-o (x' & y').
    Proof.
      intros A B; apply rbps_natural_deduction_equivalence_negation.
      apply rbps_natural_deduction_equivalence_or;
        apply rbps_natural_deduction_equivalence_negation; ap.
    Defined.

    Definition rbps_natural_deduction_equivalence_equivalence (G: list P) (x x' y y':P):
      G /- x o-o x' -> G /- y o-o y' -> G /- (x o-o y) o-o (x' o-o y').
    Proof.
      intros A B; apply rbps_natural_deduction_equivalence_and;
        apply rbps_natural_deduction_equivalence_implies; ap.
    Defined.
    
  End Equivalence_in_natural_deduction.
  
End General_properties_of_the_Russell_and_Bernays_proof_system.

Section Propositional_Calculus.

  Variable propositional_variable: Type.

  Inductive Disjunction_Negation_Propositional_Formula: Type:=
  |dnpf_variable: propositional_variable -> Disjunction_Negation_Propositional_Formula
  |dnpf_disjunction: Disjunction_Negation_Propositional_Formula ->
                     Disjunction_Negation_Propositional_Formula ->
                     Disjunction_Negation_Propositional_Formula
  |dnpf_negation: Disjunction_Negation_Propositional_Formula ->
                  Disjunction_Negation_Propositional_Formula.

  Notation P:= Disjunction_Negation_Propositional_Formula.
  Notation "$ v":= (dnpf_variable v) (at level 41).
  Notation "a // b":= (dnpf_disjunction a b) (at level 43).
  Notation "! a":= (dnpf_negation a) (at level 41).
  Notation "a -o b":= (dnpf_disjunction(dnpf_negation a) b)
                        (right associativity, at level 42).
  Notation "a & b":=
    (dnpf_negation (dnpf_disjunction (dnpf_negation a) (dnpf_negation b)))
      (at level 42). 

  Notation "p o-o q":= ((p -o q) & (q -o p)) (at level 43).

  (** Below the notion of truth value is (at last) defined for a formula, over 
      an environment. An environment is simply a choice, for any propositional_variable,
      of a boolean value, true or false, attributed to that variable. The truth value
      of any formula is then defined by induction as in the following. 
   *)
  
  Fixpoint truth_value (environment: propositional_variable -> bool) (f: P): bool:=
    match f with
    | $ v => environment v
    | a // b => orb (truth_value environment a) (truth_value environment b)
    | ! c => negb (truth_value environment c)
    end.

  (** Of course here, orb false false = false, and 
      orb false true = orb true false = orb true true = true, according to the idea mentioned
      in the introduction that "X or Y" means that at least one of the claims X, Y holds.
      as for negb, we have negb true = false and negb false = true.
   *)

  Notation tautology:=  
    (fun f: P =>
       forall environment: propositional_variable -> bool, truth_value environment f = true).

  (** We define the proof system for propositional calculus, which 
   is a special case of the Russel Bernays system studied in the first part of the text.
   All the results of this first part will apply here. *)
  
  Inductive dnpf_proof: P -> Type:=
  |dnpfp_ax1: forall x:P, dnpf_proof ((x // x) -o x) 
  |dnpfp_ax2: forall x y:P, dnpf_proof (x -o (y // x)) 
  |dnpfp_ax3: forall x y:P, dnpf_proof ((x // y) -o (y // x))
  |dnpfp_ax4: forall x y z:P, dnpf_proof ((x -o y) -o ((z // x) -o (z // y)))
  |dnpfp_mp: forall x y:P, dnpf_proof (x -o y) -> dnpf_proof x -> dnpf_proof y.

  Definition Dis_Neg_Prop:=
    make_rbps P dnpf_disjunction dnpf_negation dnpf_proof dnpfp_ax1 dnpfp_ax2 dnpfp_ax3
              dnpfp_ax4 dnpfp_mp.
  
  (** The following result says that, whenever a formula is proven in the 
   system we've defined, then its truth value is true in every possible environment.
   . A formula is a tautology when it satisfy the latter. Thus it is only possible to
   prove tautologies in propositional calculus. Further in the text, we'll establish the 
   converse of this claim: that if a formula's truth value is true in every environment, 
   then this formula is provable. This last claim is usually called the (propositional) 
   completeness theorem. *)

  
  Theorem dnpf_soundness_theorem:
    forall (environment: propositional_variable -> bool) (f: P),
      dnpf_proof f -> truth_value environment f = true.
  Proof.
    intros e f p. induction p.
    simpl; destruct (truth_value e x); simpl; reflexivity.
    simpl; destruct (truth_value e x); destruct (truth_value e y); simpl; reflexivity.
    simpl; destruct (truth_value e x); destruct (truth_value e y); simpl; reflexivity.
    simpl; destruct (truth_value e x); destruct (truth_value e y); destruct (truth_value e z);
      simpl; reflexivity.
    simpl in IHp1. rewrite IHp2 in IHp1. destruct (truth_value e y). reflexivity.
    simpl in IHp1. assumption.
  Defined.

  Section Conjunctive_and_disjunctive_normal_forms.

    (** The plan we follow in order to obtain the completeness theorem is to 
     establish that every sentence is equivalent to a formula in normal conjunctive form,
     indeed for such formulas the result is intuitively obvious (think of what happens on
     a disjunction of atoms), yet rather tedious to formalize. *)
    
    Inductive atomic_conjunction: P -> Type:=
    |atc_positive_variable: forall v: propositional_variable, atomic_conjunction ($ v)
    |atc_negative_variable: forall v: propositional_variable, atomic_conjunction (! $ v)
    |atc_and: forall f g:P, atomic_conjunction f -> atomic_conjunction g ->
                            atomic_conjunction (f & g).
    
    Inductive atomic_disjunction: P -> Type:=
    |atd_positive_variable: forall v: propositional_variable, atomic_disjunction ($ v)
    |atd_negative_variable: forall v: propositional_variable, atomic_disjunction (! $ v)
    |atd_or: forall f g:P, atomic_disjunction f -> atomic_disjunction g ->
                           atomic_disjunction (f // g).

    Inductive normal_disjunctive_form: P -> Type:=
    |ndf_ac: forall f:P, atomic_conjunction f -> normal_disjunctive_form f
    |ndf_or: forall g h:P, normal_disjunctive_form g -> normal_disjunctive_form h ->
                           normal_disjunctive_form (g // h).

    Inductive normal_conjunctive_form: P -> Type:=
    |ncf_ad: forall f:P, atomic_disjunction f -> normal_conjunctive_form f
    |ncf_and: forall g h:P, normal_conjunctive_form g -> normal_conjunctive_form h ->
                            normal_conjunctive_form (g & h).

    Fixpoint atc_negation (x:P) (a: atomic_conjunction x) {struct a}:
      sigT (fun z:P => prod (atomic_disjunction z) (dnpf_proof ((! x) o-o z))).
    Proof.
      destruct a. exists (! $ v). split. apply atd_negative_variable.
      apply (rbps_natural_deduction_equivalence_reflexivity Dis_Neg_Prop nil).
      exists ($ v). split. apply atd_positive_variable.
      apply (rbps_and_intro_2 Dis_Neg_Prop).
      apply (rbps_double_negation_elimination Dis_Neg_Prop).
      apply (rbps_double_negation_introduction Dis_Neg_Prop).
      destruct (atc_negation f a1) as (cf,(df, pf)).
      destruct (atc_negation g a2) as (cg,(dg, pg)).
      exists (cf // cg). split. apply atd_or; assumption.
      apply (rbps_natural_deduction_equivalence_transitivity Dis_Neg_Prop nil)
        with (y:= (! f) // (! g)).
      apply (rbps_natural_deduction_logic Dis_Neg_Prop nil).
      apply (rbps_and_intro_2 Dis_Neg_Prop); simpl; apply (rbps_de_morgan_or Dis_Neg_Prop).
      apply (rbps_natural_deduction_equivalence_or Dis_Neg_Prop nil); assumption.
    Defined.

    Fixpoint atd_negation (x:P) (a: atomic_disjunction x) {struct a}:
      sigT (fun z:P => prod (atomic_conjunction z) (dnpf_proof ((! x) o-o z))).
    Proof.
      destruct a. exists (! $ v). split. apply atc_negative_variable.
      apply (rbps_natural_deduction_equivalence_reflexivity Dis_Neg_Prop nil).
      exists ($ v). split. apply atc_positive_variable.
      apply (rbps_and_intro_2 Dis_Neg_Prop).
      apply (rbps_double_negation_elimination Dis_Neg_Prop).
      apply (rbps_double_negation_introduction Dis_Neg_Prop).
      destruct (atd_negation f a1) as (cf,(df, pf)).
      destruct (atd_negation g a2) as (cg,(dg, pg)).
      exists (cf & cg). split. apply atc_and; assumption.
      apply (rbps_natural_deduction_equivalence_transitivity Dis_Neg_Prop nil)
        with (y:= (! f) & (! g)).
      apply (rbps_natural_deduction_logic Dis_Neg_Prop nil).
      apply (rbps_and_intro_2 Dis_Neg_Prop); simpl; apply (rbps_de_morgan_and Dis_Neg_Prop).
      apply (rbps_natural_deduction_equivalence_and Dis_Neg_Prop nil); assumption.
    Defined.

    Fixpoint ncf_negation (x:P) (n: normal_conjunctive_form x) {struct n}:
      sigT (fun z:P => prod (normal_disjunctive_form z) (dnpf_proof ((! x) o-o z))).
    Proof.
      destruct n. destruct (atd_negation f a) as (u,(p,q)). exists u.
      split. apply ndf_ac. apply p. apply q.    
      destruct (ncf_negation g n1) as (cg,(dg, pg)).
      destruct (ncf_negation h n2) as (ch,(dh, ph)).
      exists (cg // ch). split. apply ndf_or; assumption.
      apply (rbps_natural_deduction_equivalence_transitivity Dis_Neg_Prop nil)
        with (y:= (! g) // (! h)).
      apply (rbps_natural_deduction_logic Dis_Neg_Prop nil).
      apply (rbps_and_intro_2 Dis_Neg_Prop); simpl; apply (rbps_de_morgan_or Dis_Neg_Prop).
      apply (rbps_natural_deduction_equivalence_or Dis_Neg_Prop nil); assumption.
    Defined.

    Fixpoint ndf_negation (x:P) (n: normal_disjunctive_form x) {struct n}:
      sigT (fun z:P => prod (normal_conjunctive_form z) (dnpf_proof ((! x) o-o z))).
    Proof.
      destruct n. destruct (atc_negation f a) as (u,(p,q)). exists u.
      split. apply ncf_ad. apply p. apply q.    
      destruct (ndf_negation g n1) as (cg,(dg, pg)).
      destruct (ndf_negation h n2) as (ch,(dh, ph)).
      exists (cg & ch). split. apply ncf_and; assumption.
      apply (rbps_natural_deduction_equivalence_transitivity Dis_Neg_Prop nil)
        with (y:= (! g) & (! h)).
      apply (rbps_natural_deduction_logic Dis_Neg_Prop nil).
      apply (rbps_and_intro_2 Dis_Neg_Prop); simpl; apply (rbps_de_morgan_and Dis_Neg_Prop).
      apply (rbps_natural_deduction_equivalence_and Dis_Neg_Prop nil); assumption.
    Defined.

    Fixpoint ncf_or_atd_equivalent_to_ncf
             (q:P) (a: atomic_disjunction q)
             (p:P) (n: normal_conjunctive_form p) {struct n}:
      sigT (fun h: P => prod (normal_conjunctive_form h) (dnpf_proof ((q // p) o-o h))).
    Proof.
      destruct n. exists (q // f). split. apply ncf_ad; apply atd_or; assumption.
      apply (rbps_natural_deduction_equivalence_reflexivity Dis_Neg_Prop nil).
      destruct (ncf_or_atd_equivalent_to_ncf q a g n1)  as (ug, (cg, prg)).
      destruct (ncf_or_atd_equivalent_to_ncf q a h n2) as (uh, (ch, prh)).
      exists (ug & uh). split. apply ncf_and; assumption.
      apply (rbps_natural_deduction_equivalence_transitivity Dis_Neg_Prop nil)
        with (y:= (q // g) & (q // h)). 
      apply (rbps_natural_deduction_logic Dis_Neg_Prop). 
      apply (rbps_and_intro_2 Dis_Neg_Prop);
        apply (rbps_or_distributivity_over_and Dis_Neg_Prop). 
      apply (rbps_natural_deduction_equivalence_and Dis_Neg_Prop nil); assumption.
    Defined.    

    Fixpoint ncf_or_ncf_equivalent_to_ncf
             (q:P) (a: normal_conjunctive_form q)
             (p:P) (n: normal_conjunctive_form p) {struct n}:
      sigT (fun h: P => prod (normal_conjunctive_form h) (dnpf_proof ((q // p) o-o h))).
    Proof.
      destruct n. destruct (ncf_or_atd_equivalent_to_ncf f a0 q a) as (u,(v,w)).
      exists u. split. assumption. 
      apply (rbps_natural_deduction_equivalence_transitivity Dis_Neg_Prop nil)
        with (y:= (f // q)). simpl.
      apply (rbps_and_intro_2 Dis_Neg_Prop); apply dnpfp_ax3. simpl; assumption.
      destruct (ncf_or_ncf_equivalent_to_ncf q a g n1)  as (ug, (cg, prg)).
      destruct (ncf_or_ncf_equivalent_to_ncf q a h n2) as (uh, (ch, prh)).
      exists (ug & uh). split. apply ncf_and; assumption.
      apply (rbps_natural_deduction_equivalence_transitivity Dis_Neg_Prop nil)
        with (y:= (q // g) & (q // h)). 
      apply (rbps_natural_deduction_logic Dis_Neg_Prop). 
      apply (rbps_and_intro_2 Dis_Neg_Prop);
        apply (rbps_or_distributivity_over_and Dis_Neg_Prop). 
      apply (rbps_natural_deduction_equivalence_and Dis_Neg_Prop nil); assumption.
    Defined.    

    Fixpoint conversion_to_ncf_and_ndf (f: P) {struct f}:
      prod (sigT (fun h:P => prod (normal_conjunctive_form h) (dnpf_proof (f o-o h))))
           (sigT (fun k:P => prod (normal_disjunctive_form k) (dnpf_proof (f o-o k)))).
    Proof.
      destruct f. split. exists ($ p). split. apply ncf_ad; apply atd_positive_variable.
      apply (rbps_natural_deduction_equivalence_reflexivity Dis_Neg_Prop nil).
      exists ($ p). split. apply ndf_ac; apply atc_positive_variable.
      apply (rbps_natural_deduction_equivalence_reflexivity Dis_Neg_Prop nil).
      destruct (conversion_to_ncf_and_ndf f1) as ((h1,(c1,p1)),(k1,(d1,q1))).
      destruct (conversion_to_ncf_and_ndf f2) as ((h2,(c2,p2)),(k2,(d2,q2))).
      split. destruct (ncf_or_ncf_equivalent_to_ncf h1 c1 h2 c2) as (h3,(c3,p3)).
      exists h3. split. apply c3. 
      apply (rbps_natural_deduction_equivalence_transitivity Dis_Neg_Prop nil)
        with (y:= h1 // h2). 
      apply (rbps_natural_deduction_equivalence_or Dis_Neg_Prop nil); assumption. assumption.
      exists (k1 // k2). split. apply ndf_or; assumption. 
      apply (rbps_natural_deduction_equivalence_or Dis_Neg_Prop nil); assumption.
      destruct (conversion_to_ncf_and_ndf f) as ((h,(c,p)),(k,(d,q))).
      split. destruct (ndf_negation k d) as (nk,(nd,nq)). exists nk. split. assumption. 
      apply (rbps_natural_deduction_equivalence_transitivity Dis_Neg_Prop nil)
        with (y:= ! k).
      apply (rbps_natural_deduction_equivalence_negation Dis_Neg_Prop nil); assumption.
      assumption.
      destruct (ncf_negation h c) as (nh,(nc, np)).    
      exists nh. split. assumption. 
      apply (rbps_natural_deduction_equivalence_transitivity Dis_Neg_Prop nil)
        with (y:= ! h).
      apply (rbps_natural_deduction_equivalence_negation Dis_Neg_Prop nil); assumption.
      assumption.
    Defined.
    
  End Conjunctive_and_disjunctive_normal_forms.

  Section The_completeness_theorem.

    Section Abstract_membership_for_lists.

      Variable T:Type.
      Variable u:T.

      Inductive type_list_membership: list T -> Type:=
      |tlm_head: forall l: list T, type_list_membership (cons u l)
      |tlm_tail: forall (h: T) (t: list T),
          type_list_membership t -> type_list_membership (cons h t).

      Fixpoint type_list_membership_concatenation (l m:list T):
        prod
          (type_list_membership (app l m) ->
           sum (type_list_membership l) (type_list_membership m))
          (sum (type_list_membership l) (type_list_membership m) ->
           type_list_membership (app l m)).
      Proof.
        split. induction l. simpl. intros; right; assumption.
        simpl. intro D. inversion D. left; rewrite <- H0; apply tlm_head.
        apply type_list_membership_concatenation in X. destruct X.
        left; apply tlm_tail; assumption. right; assumption.
        intro A; destruct A as [B| C]. induction B. simpl; apply tlm_head.
        simpl; apply tlm_tail; assumption. induction l. simpl; assumption.
        simpl; apply tlm_tail; assumption.
      Defined.

      Variable eqt_dec: forall (p q:T), sumbool (p = q) (p <> q).

      Fixpoint type_list_membership_dec (l:list T) {struct l}:
        sum (type_list_membership l) (type_list_membership l -> Empty_set): Type.
      Proof.
        destruct l. simpl; right; intro F; inversion F. destruct (eqt_dec u t).
        rewrite <- e; left; apply tlm_head.
        destruct (type_list_membership_dec l) as [mY|mN]. left; apply tlm_tail; assumption.
        right; intro F; inversion F; contradiction.
      Defined.

      Fixpoint type_list_membership_bool_dec (l:list T) {struct l}:=
        match l with
        | nil => false
        | cons h t =>
          match (eqt_dec u h) with
          | left _ => true
          | right_ => type_list_membership_bool_dec t
          end
        end.

      Definition bool_to_tlm_type (b:bool) (l:list T):Type:=
        match b with
        | true => type_list_membership l
        | false => type_list_membership l -> Empty_set
        end.

      Fixpoint tlmd_reflection (l:list T) {struct l}:
        bool_to_tlm_type (type_list_membership_bool_dec l) l.
      Proof.
        destruct l. simpl. intro F. inversion F. simpl.
        assert (bool_to_tlm_type (type_list_membership_bool_dec l) l)as E.
        apply tlmd_reflection.
        destruct (eqt_dec u t). simpl.
        rewrite <- e; apply tlm_head. destruct (type_list_membership_bool_dec l). simpl in E.
        apply tlm_tail; assumption. simpl; simpl in E. intro F. inversion F.
        contradiction. apply E; assumption.
      Defined.        
      
    End Abstract_membership_for_lists.

    Variable propvar_eqdec: forall v w: propositional_variable, sumbool (v = w) (v <> w).

    Definition bool_eqdec (x y:bool): sumbool (x = y) (x <> y).
    Proof.
      intros. destruct x. destruct y. left; reflexivity. right; discriminate.
      destruct y. right; discriminate. left; reflexivity.
    Defined.
    
    Definition bool_pv_eqdec (r s: prod bool propositional_variable):
      sumbool (r = s) (r <> s).
    Proof.
      destruct r as (rb, rv). destruct s as (sb, sv). destruct (propvar_eqdec rv sv).
      destruct (bool_eqdec rb sb). left; rewrite e; rewrite e0; reflexivity.
      right; intro F; inversion F; contradiction.
      right; intro F; inversion F; contradiction.
    Defined.
    
    Section The_atomic_disjunctive_case.

      Fixpoint atd_list (f: P) (a: atomic_disjunction f) {struct a}:
        list (prod bool propositional_variable) :=
        match a with
        | atd_positive_variable v => ((true, v) :: nil)%list
        | atd_negative_variable v => ((false, v) :: nil)%list
        | atd_or f0 g a1 a2 => (atd_list f0 a1 ++ atd_list g a2)%list
        end.
      
      Inductive signed_atom_belongs (v: propositional_variable):
        forall (b: bool) (f: P), atomic_disjunction f -> Type:=
      |sab_atom_true: signed_atom_belongs v true ($ v) (atd_positive_variable v)
      |sab_atom_false: signed_atom_belongs v false (! ($ v)) (atd_negative_variable v)
      |sab_left: forall (c: bool) (fl fr: P)
                        (al: atomic_disjunction fl) (ar: atomic_disjunction fr),
          signed_atom_belongs v c fl al ->
          signed_atom_belongs v c (fl // fr) (atd_or fl fr al ar)
      |sab_right: forall (c: bool) (fl fr: P)
                         (al: atomic_disjunction fl) (ar: atomic_disjunction fr),
          signed_atom_belongs v c fr ar ->
          signed_atom_belongs v c (fl // fr) (atd_or fl fr al ar).

      Definition atdl_sab_equivalence
                 (v:propositional_variable) (b:bool)
                 (f: P) (a: atomic_disjunction f):
        prod (signed_atom_belongs v b f a ->
              type_list_membership (prod bool propositional_variable) (b,v) (atd_list f a))
             (type_list_membership (prod bool propositional_variable) (b,v) (atd_list f a) ->
              signed_atom_belongs v b f a).
      Proof.
        split. intro sab. induction sab. simpl; apply tlm_head. simpl; apply tlm_head.
        simpl; apply type_list_membership_concatenation; left; assumption.
        simpl; apply type_list_membership_concatenation; right; assumption.
        induction a. simpl; intro D; inversion D. apply sab_atom_true. inversion X.
        simpl; intro D; inversion D. apply sab_atom_false. inversion X.
        simpl. intro E. apply type_list_membership_concatenation in E.
        destruct E as [Ef | Eg]. apply sab_left; apply IHa1; assumption.
        apply sab_right; apply IHa2; assumption.
      Defined.        

      Definition list_to_refutation_environment
                 (l: list (prod bool propositional_variable))
                 (w: propositional_variable): bool:=
        type_list_membership_bool_dec
          (prod bool propositional_variable) (false, w) bool_pv_eqdec l.      

      Definition refutation_environment (f: P) (a: atomic_disjunction f):
        propositional_variable -> bool:=
        list_to_refutation_environment (atd_list f a).               
      
      Fixpoint decision_lbp_complete (l: list (prod bool propositional_variable)) {struct l}:
        sum
          (sigT (fun v: propositional_variable =>
                   prod
                     (type_list_membership (prod bool propositional_variable) (true, v) l)
                     (type_list_membership (prod bool propositional_variable) (false, v) l)) )
          (forall w: propositional_variable,
              type_list_membership (prod bool propositional_variable) (true, w) l ->
              type_list_membership (prod bool propositional_variable) (false, w) l ->
              Empty_set).
      Proof.
        destruct l. right. intros w F. inversion F.
        destruct (decision_lbp_complete l) as [Y|N].
        destruct Y as (x, (yx, nx)). left. exists x. split; apply tlm_tail; assumption.
        destruct p as (b,w).
        destruct
          (type_list_membership_dec (prod bool propositional_variable)
                                    ((negb b), w) bool_pv_eqdec l)
          as [ypl | npl]. left. exists w. destruct b. split. apply tlm_head.
        apply tlm_tail; simpl in ypl; assumption. split.
        apply tlm_tail; simpl in ypl; assumption. apply tlm_head. right.
        intros x FL FR. destruct b. simpl in npl. inversion FR. inversion FL. apply npl.
        rewrite <- H2; assumption. apply (N x); assumption.
        simpl in npl. inversion FL. inversion FR. apply npl.
        rewrite <- H2; assumption. apply (N x); assumption.
      Defined.

      Definition decision_atd_complete (f: P) (a: atomic_disjunction f):        
        sum
          (sigT (fun v: propositional_variable =>
                   prod
                     (signed_atom_belongs v true f a)
                     (signed_atom_belongs v false f a)))
          (forall w: propositional_variable,
              type_list_membership
                (prod bool propositional_variable) (true, w) 
                (atd_list f a) ->
              type_list_membership
                (prod bool propositional_variable) (false, w)
                (atd_list f a) ->
              Empty_set).
      Proof.
        destruct (decision_lbp_complete (atd_list f a)) as [Y|N].
        destruct Y as (w,(p, q)).
        apply atdl_sab_equivalence in p;
          apply atdl_sab_equivalence in q; left; exists w; split; assumption.
        right; assumption.
      Defined.

      Definition orb_false_sufficient_condition (x y:bool):
        x = false -> y = false -> orb x y = false.
      Proof.
        intros ex ey; rewrite ex; rewrite ey; simpl; reflexivity.
      Defined.

      Fixpoint bool_pv_list_truth_value (env: propositional_variable -> bool)
               (l: list (prod bool (propositional_variable))) {struct l}: bool:=
        match l with
        | nil => false
        | cons h t =>
          match (fst h) with
          |true => orb (env (snd h)) (bool_pv_list_truth_value env t)
          |false => orb (negb (env (snd h))) (bool_pv_list_truth_value env t)
          end
        end.

      Fixpoint bpltv_concatenation (env: propositional_variable -> bool)
               (l m:list (prod bool propositional_variable)) {struct l}:
        bool_pv_list_truth_value env (app l m) =
        orb (bool_pv_list_truth_value env l) (bool_pv_list_truth_value env m).
      Proof.
        destruct l. simpl; reflexivity. simpl.
        destruct p. simpl. destruct b. destruct (env p). simpl; reflexivity.
        simpl; apply bpltv_concatenation. destruct (negb (env p)). simpl; reflexivity.
        simpl; apply bpltv_concatenation.
      Defined.
      
      Fixpoint bpltv_identity (env: propositional_variable -> bool)
               (f: P) (a: atomic_disjunction f) {struct a}: 
        truth_value env f = bool_pv_list_truth_value env (atd_list f a).
      Proof.
        destruct a. simpl. destruct (env v); simpl; reflexivity. simpl.
        destruct (env v); simpl; reflexivity.
        simpl. rewrite bpltv_concatenation.
        apply f_equal2; apply bpltv_identity.
      Defined.
      
      Lemma sufficient_condition_for_false_environment
            (env: propositional_variable -> bool)
            (l: list (prod bool propositional_variable)):
        (forall w: propositional_variable,
            type_list_membership (prod bool propositional_variable) ((env w), w) l ->
            Empty_set) ->
        bool_pv_list_truth_value env l = false.
      Proof.
        induction l. intros; simpl; reflexivity. intro D. simpl. destruct a as (b,v).
        assert (env v = true \/ env v = false) as A. destruct (env v). left; reflexivity.
        right; reflexivity. simpl.  destruct b. apply orb_false_sufficient_condition.
        destruct A as [A1|A2]. apply Empty_set_rec. apply (D v). rewrite A1; apply tlm_head.
        assumption. apply IHl; intros w M; apply Empty_set_rec; apply (D w);
                      apply tlm_tail; assumption. destruct A as [A3|A4]. rewrite A3. simpl.
        apply IHl; intros w M; apply Empty_set_rec; apply (D w); apply tlm_tail; assumption.
        apply Empty_set_rec; apply (D v); rewrite A4; apply tlm_head.
      Defined.        
      
      Theorem clean_list_refutation_value_environment
              (l: list (prod bool propositional_variable)):
        (forall w: propositional_variable,
            type_list_membership (prod bool propositional_variable) (true, w) l ->
            type_list_membership (prod bool propositional_variable) (false, w) l ->
            Empty_set) ->
        bool_pv_list_truth_value (list_to_refutation_environment l) l = false.
      Proof.
        intro A. apply sufficient_condition_for_false_environment. intros w B. 
        unfold list_to_refutation_environment in B.
        assert (bool_to_tlm_type
                  (prod bool propositional_variable)
                  (false, w)
                  (type_list_membership_bool_dec (prod bool propositional_variable)
                                                 (false, w) bool_pv_eqdec l)
                  l)  as L. apply tlmd_reflection.
        destruct (type_list_membership_bool_dec (bool * propositional_variable) 
                                                (false, w) bool_pv_eqdec l).
        simpl in L. apply (A w); assumption. simpl in L. apply L; assumption.
      Defined.        

      Fixpoint proof_of_atomic_disjunctions_from_atoms
               (v: propositional_variable) (b:bool)
               (f:P) (a: atomic_disjunction f) 
               (s: signed_atom_belongs v b f a) {struct s}:
        dnpf_proof ((match b with |true => $ v |false => (! $ v) end) -o f).
      Proof.
        destruct s. apply (rbps_identity Dis_Neg_Prop). apply (rbps_identity Dis_Neg_Prop).
        apply (rbps_syllogism Dis_Neg_Prop) with (y := fl).
        apply (proof_of_atomic_disjunctions_from_atoms v c fl al s). 
        apply (rbps_or_left_intro Dis_Neg_Prop).
        apply (rbps_syllogism Dis_Neg_Prop) with (y := fr).
        apply (proof_of_atomic_disjunctions_from_atoms v c fr ar s). 
        apply (rbps_axiom_scheme_2 Dis_Neg_Prop).
      Defined.
      
      Definition constructive_completeness_for_atomic_disjunctions:
        forall (f: P),
          atomic_disjunction f ->
          sum (dnpf_proof f)
              (sig (fun (environment: propositional_variable -> bool) =>
                      (truth_value environment f = false))).
      Proof.
        intros f a. destruct (decision_atd_complete f a) as [L|R]. left.
        destruct L as (v, (st,sf)). apply (rbps_excluded_middle Dis_Neg_Prop (! $ v)).  simpl.
        apply proof_of_atomic_disjunctions_from_atoms with (b:= true) (a := a); assumption.
        apply proof_of_atomic_disjunctions_from_atoms with (b:= false) (a := a); assumption.
        right. exists (refutation_environment f a). unfold refutation_environment.
        rewrite bpltv_identity with (a:= a); apply clean_list_refutation_value_environment;
          assumption.
      Defined.
      
    End The_atomic_disjunctive_case.

    Section Completeness_for_normal_conjunctive_forms.

      Fixpoint constructive_completeness_for_normal_conjunctive_forms
               (f: P) (n: normal_conjunctive_form f):
        sum (dnpf_proof f)
            (sig (fun (environment: propositional_variable -> bool) =>
                    (truth_value environment f = false))).
      Proof.
        destruct n. apply constructive_completeness_for_atomic_disjunctions; assumption.
        destruct (constructive_completeness_for_normal_conjunctive_forms g n1) as [pg|rg].
        destruct (constructive_completeness_for_normal_conjunctive_forms h n2) as [ph|rh].
        left. apply (rbps_and_intro_2 Dis_Neg_Prop); assumption.
        right; destruct rh as (eh, prh); exists eh; simpl; rewrite prh;
          destruct (truth_value eh g); simpl; reflexivity.
        right; destruct rg as (eg, prg); exists eg; simpl; rewrite prg; simpl; reflexivity.
      Defined.
      
    End Completeness_for_normal_conjunctive_forms.

    Definition provable_equivalence_with_truth_values:
      forall (a b: P) (env: propositional_variable -> bool),
        dnpf_proof (a o-o b) -> truth_value env a = truth_value env b.
    Proof.
      intros a b env A. apply (dnpf_soundness_theorem env) in A. simpl in A.
      assert (false = true -> truth_value env a = truth_value env b) as B.
      intros. absurd (false = true). discriminate. assumption.
      destruct (truth_value env a).
      destruct (truth_value env b). reflexivity. simpl in A; apply B; assumption. 
      destruct (truth_value env b). simpl in A; apply B; assumption. reflexivity.
    Defined.      

    (** The completeness theorem is eventually proven below. *)
    
    Definition constructive_propositional_completeness (f: P):
        sum (dnpf_proof f)
            (sig (fun (environment: propositional_variable -> bool) =>
                    (truth_value environment f = false))).
    Proof.
      destruct (conversion_to_ncf_and_ndf f) as ((c, (nc, ec)), (d, (nd, ed))).
      destruct (constructive_completeness_for_normal_conjunctive_forms c nc)
        as [prc| re]. left.
      apply (rbps_natural_deduction_equivalence_right_left_elim Dis_Neg_Prop nil) with (y:= c);
        simpl; assumption. right. destruct re as (renv, eenv). exists renv.
      rewrite (provable_equivalence_with_truth_values f c renv ec); assumption.
    Defined.

    Theorem propositional_completeness (f: P):
      (forall environment: propositional_variable -> bool, truth_value environment f = true)
      <->
      (inhabited (dnpf_proof f)).
    Proof.
      split. intro A. destruct (constructive_propositional_completeness (f: P)) as [L|R].
      apply (inhabits L). apply False_rect. destruct R as (zzz, e). absurd (true = false).
      discriminate. rewrite A in e; assumption. intro i. induction i.
      intro env; apply dnpf_soundness_theorem; assumption.
    Defined.
     
  End The_completeness_theorem.  
  
End Propositional_Calculus.
