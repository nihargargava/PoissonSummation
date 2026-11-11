import Mathlib.Analysis.Distribution.SchwartzSpace.Basic
import Mathlib.Analysis.Distribution.SchwartzSpace.Fourier
import Mathlib.Analysis.Fourier.PoissonSummation



variable (d : ℕ)

--- V d means R^d

abbrev V d := EuclideanSpace ℝ (Fin d)

-- Sch d should mean d dimensional Schartz functions 
abbrev Sch d := SchwartzMap ( V d ) ℂ 


--- This is my Fourier transform!
noncomputable def Fr : Sch d → Sch d := 
  fun ( f : Sch d ) => SchwartzMap.fourierTransformCLM ℂ (V := V d) ( E:= ℂ ) f



----------- FOOLING AROUND -------------
--- Let's define Fourier transform for a one-dimensional function
variable (f : Sch 1)


variable ( a : ℝ )

--- This is how it works!
#check ( !₂[a] : V 1 )

#check ( 0 : V 1 )

-- I can call values of a function?
#check (f 0 : ℂ) 
#check ( Fr 1 f 0 : ℂ )
#check (tsum fun (n : ℤ ) => f (!₂[n]))
#check (tsum fun (n : ℤ ) => Fr 1 f (!₂[n]))


--- This is failing
-- #check ( ( fun (x : ℝ ) => f !₂[x]  ) : SchwartzMap ℝ ℂ )

--- So I have to do show that V 1 ≃ ℝ manually. That's saying that ℝ¹ ≃ ℝ 
noncomputable def onedim (f : Sch 1 ) : SchwartzMap ℝ ℂ where
  toFun := fun (x : ℝ) => f !₂[x] 
  smooth' := by 
    -- f is already smooth function on V 1
    have fsmooth := f.smooth'
    -- I have to use composition 
    apply fsmooth.comp
    refine contDiff_piLp' 2 ?_
    intro i
    simp only [Matrix.cons_val_fin_one]
    exact contDiff_fun_id
  decay' := by
    have fdecay := f.decay'
    intro k n
    rcases fdecay k n with ⟨ C , hC ⟩ 
    refine ⟨ C , ?_ ⟩
    intro x
    rcases hC !₂[x] with hy
    have equalnorm : ‖x‖ = ‖!₂[x]‖  := by sorry
    have samenumber : ( fun x => f !₂[x] ) x = (f.toFun !₂[x]) := by sorry
    rw [equalnorm,samenumber]








    




  --- But this function is just ℝ → ℂ 



#check ( freal f : SchwartzMap ℝ ℂ )


-- #check SchwartzMap.tsum_eq_tsum_fourier f

-- Boring theorem to see if I know any lean at all
theorem boring (f : Sch d ) : f = f := by 
  rfl

--- This will become Poisson summation eventually
-- Let's restate the version for d=1
theorem OneDimPoisson (f : Sch 1 ) : 
  (tsum fun (n : ℤ ) => f (!₂[n])) = (tsum fun (ξ : ℤ ) => Fr 1 f (!₂[ξ]))
    := by
  sorry
  
------------ END OF FOOLING AROUND ------------



 





