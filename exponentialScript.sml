
Definition is_iso_def:
is_iso f ⇔ (∃f'. dom f' = cod f ∧ cod f = dom f ∧ f o f' = id (cod f) ∧ f' o f = id (dom f))
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
  
Theorem singleton_is_mono:
∀B. is_mono (transpose (char (product_induce (id B) (id B))))
Proof
cheat
QED

val _ = clear_overloads_on "×";
        
Overload product_obj = “λA B. dom (SND (product A B))”
val _ = add_rule {block_style = (AroundEachPhrase, (PP.CONSISTENT, 0)),
                  fixity = Infix (NONASSOC,450), 
                  pp_elements = [TOK "×"], 
                  term_name = "product_obj", paren_style = OnlyIfNecessary}     
        
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
>- 


                  
