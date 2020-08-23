val _ = new_type ("arrow", 0)
val _ = new_type ("object", 0)

val _ = new_constant("id", ``:object -> arrow``)
val _ = new_constant("arrow_compose", ``:arrow -> arrow -> arrow``);

val _ = new_constant("dom", “:arrow -> object”)
val _ = new_constant("cod", “:arrow -> object”)

Overload "o" = ``arrow_compose``

(*identity*)         

val id1 = new_axiom("id1", ``!X. dom (id X) = X ∧ cod (id X) = X``)

val idL = new_axiom("idL", ``!X a. cod a = X ==> (id X) o a = a``);

val idR = new_axiom("idR", ``!X a. dom a = X ==> a o (id X) = a``);

(*composition*)     

val compose = new_axiom("compose", ``!f g. cod f = dom g ⇒ dom (g o f) = dom f ∧ cod (g o f) = cod g``);

val compose_assoc = new_axiom("compose_assoc",
                  “∀f g h. cod f = dom g ∧ cod g = dom h ⇒
                           (h o g) o f = h o (g o f)”)
                           
(* product*)

val product = new_constant("product", “:object -> object -> (arrow # arrow)”)                          
    
val product_up = new_axiom("product_up",
                          “∀A B. dom (FST (product A B)) = dom (SND (product A B)) ∧
                                 cod (FST (product A B)) = A ∧
                                 cod (SND (product A B)) = B ∧
                                 (∀f g. dom f = dom g ∧ cod f = A ∧ cod g = B ⇒
                                        ∃!u. dom u = dom g ∧ cod u = dom (SND (product A B)) ∧
                                             f = (FST (product A B)) o u ∧
                                             g = (SND (product A B)) o u)        
                                              
                          ”)

(*add the notion of induced arrow in order to define iv in page 163*)

val product_induce = new_constant("product_induce", “:arrow -> arrow -> arrow”)      

val product_induce_def = new_axiom("product_induce_def",
                          “∀A B. dom (FST (product A B)) = dom (SND (product A B)) ∧
                                 cod (FST (product A B)) = A ∧
                                 cod (SND (product A B)) = B ∧
                                 (∀f g. dom f = dom g ∧ cod f = A ∧ cod g = B ⇒
                                        dom (product_induce f g) = dom g ∧
                                        cod (product_induce f g) = dom (SND (product A B)) ∧
                                        f = (FST (product A B)) o (product_induce f g) ∧
                                        g = (SND (product A B)) o (product_induce f g))        
                                              
                          ”)                                             
                                                                  
(* pullback *)


val pullback = new_constant("pullback", “: arrow -> arrow -> (arrow # arrow)”)

val pullback_up = new_axiom("pullback_up",
                  “∀f g.
                     cod f = cod g ⇒
                     dom (FST (pullback f g)) = dom (SND (pullback f g)) ∧
                     cod (FST (pullback f g)) = dom f ∧
                     cod (SND (pullback f g)) = dom g ∧
                     f o (FST (pullback f g)) = g o (SND (pullback f g)) ∧
                     (∀x1 x2. dom x1 = dom x2 ∧ cod x1 = dom f ∧ cod x2 = dom g ∧ f o x1 = g o x2 ⇒
                              ∃!u. dom u = dom x2 ∧ cod u = dom (SND (pullback f g)) ∧
                                   (FST (pullback f g)) o u = x1 ∧
                                   (SND (pullback f g)) o u = x2
                     )
                  ”)

(*add the notion of "is pullback" as a definition in order to define iii in page 163*)

(*define in that way so rw etc will use def to decompose a map as factors through certain objects*)      

Definition is_pullback_def:
is_pullback f g (pb1, pb2) ⇔ cod f = cod g ∧ dom pb1 = dom pb2 ∧ cod pb1 = dom f ∧
                             cod pb2 = dom g ∧ f o pb1 = g o pb2 ∧
                             (∀x1 x2. dom x1 = dom x2 ∧ cod x1 = dom f ∧ cod x2 = dom g ∧
                                      f o x1 = g o x2 ⇒
                                      ∃!u. dom u = dom x2 ∧ cod u = dom pb2 ∧
                                           x1 = pb1 o u ∧
                                           x2 = pb2 o u)
End

                                                     
(*terminal object*)

val terminal = new_constant("terminal", “: object”)

val terminal_def = new_axiom("terminal_def", “∀X. ∃!u. dom u = X ∧ cod u = terminal”)

(*add a constant for the unique arrow to terminal object, in order to define the true map*)    

val X2t = new_constant("X2t", “:object -> arrow”)

val X2t_def = new_axiom("X2t_def",“∀X. dom (X2t X) = X ∧ cod (X2t X) = terminal”)                                        
(* mono *)

Definition is_mono_def:   
  is_mono f ⇔
  ∀g1 g2. dom g1 = dom g2 ∧ cod g1 = dom f ∧ cod g2 = dom f ∧
          f o g1 = f o g2 ⇒ g1 = g2
End                                                                                                                  
(*subobject classifier + truth map*)

val _ = new_constant("true", “: arrow”)

(*add subobject classifier as primitive notion in order to define iv in p163*)

val _ = new_constant("omega", “: object”)      

val true_def = new_axiom("true_def", “is_mono true ∧ dom true = terminal ∧ cod true = omega ∧
                              ∀m. is_mono m ⇒
                                  ∃!char. dom char = cod m ∧ cod char = omega ∧
                                          is_pullback char true (m, (X2t (dom m)))”)

val _ = new_constant("char", “:arrow -> arrow”)

val char_def = new_axiom("char_def", “∀m. is_mono m ⇒
                                          dom (char m) = cod m ∧ cod (char m) = omega ∧
                                          is_pullback (char m) true (m, (X2t (dom m)))”)                                              
(*power object*)

val _ = new_constant("pow", “: object -> object”)

val _ = new_constant("mem", “: object -> arrow”)

val mem_def = new_axiom("mem_def",
                       “∀B. dom (mem B) = dom (SND (product B (pow B))) ∧ cod (mem B) = omega ∧
                            (∀A f. dom f = dom (SND (product B A)) ∧ cod f = omega ⇒
                                ∃!g. dom g = A ∧ cod g = pow B ∧
                                    f = (mem B) o
                                        product_induce (FST (product B A))
                                                       (g o (SND (product B A))))”)    

                       
val _ = new_constant("transpose", “:arrow -> arrow”)

val transpose_def = new_axiom("transpose_def",
                             “(∀B A f. dom f = dom (SND (product B A)) ∧ cod f = omega ⇒
                                       dom (transpose f) = A ∧ cod (transpose f) = pow B ∧
                                       f = (mem B) o
                                        product_induce (FST (product B A))
                                                       ((transpose f) o (SND (product B A))))”)    
val _ = add_rule {block_style = (AroundEachPhrase, (PP.CONSISTENT, 0)),
                  fixity = Closefix, 
                  pp_elements = [TOK "⟨", TM, TOK ",",TM, TOK "⟩"], 
                  term_name = "product_induce", paren_style = OnlyIfNecessary}

Definition is_iso_def:
is_iso f ⇔ (∃f'. dom f' = cod f ∧ cod f' = dom f ∧ f o f' = id (cod f) ∧ f' o f = id (dom f))
End

        
Definition are_iso_def:
are_iso A B ⇔ ∃f g. dom f = A ∧ cod f = B ∧ dom g = B ∧ cod g = A ∧
                    f o g = id B ∧ g o f = id A
End


val _ = add_rule {block_style = (AroundEachPhrase, (PP.CONSISTENT, 0)),
                  fixity = Infix (NONASSOC,450), 
                  pp_elements = [TOK "≅"], 
                  term_name = "are_iso", paren_style = OnlyIfNecessary}                                      

(*axioms end*)



(*char required for this part,transpose required for this part*)

Theorem product_with_terminal:
∀B. is_iso (FST (product B terminal))
Proof
rw[is_iso_def,product_up] >> qexists_tac ‘⟨id B, X2t B⟩’ >> rw[] (* 4 *)
>- metis_tac[product_induce_def,id1,X2t_def]
>- metis_tac[product_induce_def,id1,X2t_def]
>- metis_tac[product_induce_def,id1,X2t_def]
>- (‘dom (id (B x terminal)) = dom (SND (product B terminal)) ∧
    cod (id (B x terminal)) = (B x terminal) ∧
    FST (product B terminal) = FST (product B terminal) ∘ (id (B x terminal)) ∧
    SND (product B terminal) = SND (product B terminal) ∘ (id (B x terminal)) ∧
    
    dom (⟨id B,X2t B⟩ ∘ FST (product B terminal)) = dom (SND (product B terminal)) ∧
    cod (⟨id B,X2t B⟩ ∘ FST (product B terminal)) = (B x terminal) ∧
    FST (product B terminal) = FST (product B terminal) ∘ (⟨id B,X2t B⟩ ∘ FST (product B terminal))∧
    SND (product B terminal) = SND (product B terminal) ∘ (⟨id B,X2t B⟩ ∘ FST (product B terminal))’ suffices_by
    (‘dom (FST (product B terminal)) = dom (SND (product B terminal)) ∧
    cod (FST (product B terminal)) = B ∧
    cod (SND (product B terminal)) = terminal’ by metis_tac[product_up] >>
    ‘∃!u.
                 dom u = dom (SND (product B terminal)) ∧ cod u = (B x terminal) ∧
                 (FST (product B terminal)) = FST (product B terminal) ∘ u ∧
                 (SND (product B terminal)) = SND (product B terminal) ∘ u’ by fs[product_up] >>
     metis_tac[EXISTS_UNIQUE_THM]) >> 
    simp[product_induce_def,id1,X2t_def,idL,idR,idL] >>
    ‘dom (FST (product B terminal)) = (B x terminal) ∧
    cod ⟨id B,X2t B⟩ = (B x terminal) ∧
    dom ⟨id B,X2t B⟩ = B ∧ cod (FST (product B terminal)) = B’
    by fs[product_up,product_induce_def,id1,X2t_def] >>
    rw[] (* 4 *)
    >- metis_tac[compose]
    >- metis_tac[compose]
    >- (‘FST (product B terminal) ∘ ⟨id B,X2t B⟩ ∘ FST (product B terminal) =
        (FST (product B terminal) ∘ ⟨id B,X2t B⟩) ∘ FST (product B terminal)’
         suffices_by 
         (rw[] >>
         ‘FST (product B terminal) ∘ ⟨id B,X2t B⟩ = id B’ by fs[product_induce_def,id1,X2t_def] >>
         rw[idL]) >>
       ‘(FST (product B terminal) ∘ ⟨id B,X2t B⟩) ∘ FST (product B terminal) =
        FST (product B terminal) ∘ ⟨id B,X2t B⟩ ∘ FST (product B terminal)’
        suffices_by metis_tac[] >> irule compose_assoc >>
        fs[product_induce_def,id1,X2t_def])
     >- (‘dom (SND (product B terminal)) =
         dom (SND (product B terminal) ∘ ⟨id B,X2t B⟩ ∘ FST (product B terminal)) ∧
         cod (SND (product B terminal)) = terminal ∧
         cod (SND (product B terminal) ∘ ⟨id B,X2t B⟩ ∘ FST (product B terminal)) = terminal’
         suffices_by
          (rw[] >>
          ‘∃!u. dom u = (B x terminal) ∧ cod u = terminal’ by metis_tac[terminal_def] >>
          fs[EXISTS_UNIQUE_THM]) >>
         rw[] (* 3 *) >>
         fs[product_induce_def,id1,X2t_def,compose]))
QED
        
Theorem dom_terminal_mono:
∀f. dom f = terminal ⇒ is_mono f
Proof
rw[is_mono_def] >> metis_tac[terminal_def]
QED

Theorem pullback_mono_mono:
∀m. is_mono m ⇒ ∀f pb1 pb2. is_pullback f m (pb1, pb2) ⇒ is_mono pb1
Proof
rw[is_pullback_def,is_mono_def] >>
‘f o pb1 o g1 = f o pb1 o g2’ by simp[] >>
‘f o pb1 o g1 = (f o pb1) o g1 ∧ f o pb1 o g2 = (f o pb1) o g2’ by metis_tac[compose_assoc] >>
‘(m o pb2) o g1 = (m o pb2) o g2’ by metis_tac[] >>
rfs[compose_assoc] >> ‘pb2 ∘ g1 = pb2 ∘ g2’ by metis_tac[compose] >>
first_x_assum (qspecl_then [‘pb1 o g1’,‘pb2 o g1’] mp_tac) >> rw[compose] >>
‘f ∘ pb1 ∘ g2 = (f ∘ pb1) ∘ g2 ∧
 m ∘ pb2 ∘ g2 = (m ∘ pb2) ∘ g2’
 by fs[compose_assoc] >>
‘f ∘ pb1 ∘ g2 = m ∘ pb2 ∘ g2’ by metis_tac[] >> fs[] >>
metis_tac[EXISTS_UNIQUE_THM]
QED       
              
Theorem singleton_is_mono:
∀B. is_mono (transpose (char (product_induce (id B) (id B))))
Proof
cheat
QED

val _ = clear_overloads_on "x";
        
Overload product_obj = “λA B. dom (SND (product A B))”
val _ = add_rule {block_style = (AroundEachPhrase, (PP.CONSISTENT, 0)),
                  fixity = Infix (NONASSOC,450), 
                  pp_elements = [TOK "×"], 
                  term_name = "product_obj", paren_style = OnlyIfNecessary}     


(*need lemma pullback of mono is mono*)
                  
Theorem exponential_exists:
∀B C. ∃B2C e.
        dom e = dom (SND (product B B2C)) ∧ cod e = C ∧
        ∀f A. dom f = dom (SND (product B A)) ∧ cod f = C ⇒
            ∃!g. dom g = A ∧ cod g = B2C ∧
                 f = e o ⟨FST (product B A), g o (SND (product B A))⟩
Proof
rw[] >>
‘∃f. is_iso f ∧ dom f = ((C x B) x (pow (C x B))) ∧ cod f = (C x (B x (pow (C x B))))’ by cheat >>
‘∃i. is_iso i ∧ (dom i = (B x terminal)) ∧ cod i = B’ by cheat >>
qabbrev_tac ‘v = transpose (f o (mem (B x C)))’ >>
qabbrev_tac ‘σ = char (transpose (char (product_induce (id C) (id C))))’ >>
qabbrev_tac ‘u = transpose (σ o v)’ >>
qabbrev_tac ‘h = transpose (i o (X2t B) o true)’ >>
qabbrev_tac ‘BC = dom (SND (pullback u h))’
qexists_tac ‘BC’ >>
qabbrev_tac ‘m = SND (pullback u h)’ >>
‘v o ⟨FST (product B BC),m o (SND (product B BC))⟩ =
true o (X2t (B x terminal)) o ⟨FST (product B BC), (X2t BC) o (SND (product B BC))⟩’ by cheat >>
‘is_pullback σc true (σ,X2t C)’  by cheat  >>
‘∃!e. dom e = (B x BC) ∧ cod e = C ∧ σ o e = v o ⟨FST (product B BC),m o (SND (product B BC))⟩’  by cheat >>
fs[Once EXISTS_UNIQUE_THM] >>
qexists_tac ‘e’ >> rpt strip_tac

metis_tac[] cheat

(*two nontrivial ones*)
>- ‘σ o f' = σ o (e ∘ ⟨FST (product B A),g ∘ SND (product B A)⟩) ∧
    σ o f' = σ o (e ∘ ⟨FST (product B A),g' ∘ SND (product B A)⟩)’ by metis_tac[] >>
   ‘’


                  
