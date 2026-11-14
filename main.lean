import Mathlib.Analysis.Distribution.SchwartzSpace.Basic
import Mathlib.Analysis.Distribution.SchwartzSpace.Fourier
import Mathlib.Analysis.Fourier.PoissonSummation


--- d for dimension
variable (d : ℕ)

--- V d means ℝᵈ 
abbrev V d := EuclideanSpace ℝ (Fin d)

--- V 1 is the same as ℝ 
--- Let's quickly prove that there is an isomorphism between V 1 and ℝ 
--- The linear isomorphisms between V 1 and ℝ have type V 1 ≃L[ℝ] ℝ 
--- Here's the nerdy way to define this isomorphism
def E : ℝ ≃ₗᵢ[ℝ] V 1 := 
  {
    --- must fill the fields from
    -- #print LinearIsometryEquiv
    toFun := fun x => !₂[x]
    invFun := fun v => v 0
    right_inv := by
      --- Chasing a bunch of rw, simp, etc.
      intro h
      simp_all only [Fin.isValue]
      rw [@PiLp.ext_iff]
      intro i
      simp only [Fin.isValue, Matrix.cons_val_fin_one] 
      rw [← Fin.eq_zero i]
    map_add' := by
      --- Chasing a bunch of rw, simp, etc.
      refine fun x y => ?_
      rw [@PiLp.ext_iff] 
      intro i
      simp only [Matrix.cons_val_fin_one, PiLp.add_apply]
    map_smul' := by
      --- Chasing a bunch of rw, simp, etc.
      intro m x 
      simp only [smul_eq_mul, RingHom.id_apply] 
      rw [@PiLp.ext_iff] 
      intro i
      simp only [Matrix.cons_val_fin_one, PiLp.smul_apply, smul_eq_mul]

    norm_map' := by
      intro x
      --- This took me so long to figure out!
      --- Basically change allows us to guess an equivalent statement for the goal
      --- And we can just claim the goal to be this (if it is true)
      change ‖!₂[x]‖ = ‖x‖
      --- chasing simp?, rw?, apply? etc.
      simp [Real.norm_eq_abs] 
      simp [EuclideanSpace.norm_eq]
      exact Real.sqrt_sq_eq_abs x 
  }


-- Sch d should mean d dimensional Schwartz functions 
--- The Schwartz functons are complex valued
abbrev Sch d := SchwartzMap ( V d ) ℂ 

--- This is my Fourier transform!
--- It relies on appealing to mathlib
noncomputable def Fr : Sch d → Sch d := 
  fun ( f : Sch d ) => FourierTransform.fourier f



--- This is failing. It throws a type mismatch
-- #check ( ( fun (x : ℝ ) => f !₂[x]  ) : SchwartzMap ℝ ℂ )
--- This is because lean 
--- So I have to do show that V 1 ≃ ℝ manually. That's saying that ℝ¹ ≃ ℝ 
--- So the following is a function that sends f ∈ Sch 1 to SchwartzMap ℝ ℂ 
noncomputable def onedim (f : Sch 1 ) : SchwartzMap ℝ ℂ where
  toFun := fun (x : ℝ) => f !₂[x] 
  -- I have to show that the output is Schwartz. This means I have to show that it is smooth and decays well. Clearly, I must use those properties for Sch 1 and show those for f
  smooth' := by 
    -- f is already smooth function on V 1
    have fsmooth := f.smooth'
    -- I have to use composition. 
    --- Basically f !₂[x] is a composition of two things:
    --- f and the function x ↦ !₂[x]
    --- They are both smooth
    --- first we write that f is smooth
    apply fsmooth.comp
    --- Then we massage the goal a bit
    refine contDiff_piLp' 2 ?_
    intro i
    simp only [Matrix.cons_val_fin_one]
    --- We finish because the idetity function is smooth
    exact contDiff_fun_id
  decay' := by
    --- to show decay, first I apply that f has decay
    have fdecay := f.decay'
    -- now we massage our definitions
    intro k n
    rcases fdecay k n with ⟨ C , hC ⟩ 
    refine ⟨ C , ?_ ⟩
    intro x
    rcases hC !₂[x] with hy
    --- First let us substitute ‖x‖ with ‖!₂[x]‖
    have equalnorm : ‖x‖ = ‖!₂[x]‖  := by 
      simp [Real.norm_eq_abs] 
      --- This next lemma was a bit difficult to find. I had to ask an LLM
      --- (How do people in Lean know all this? Frustrating! - Nihar)
      simp [EuclideanSpace.norm_eq]
      exact Eq.symm (Real.sqrt_sq_eq_abs x)
    rw [equalnorm]
    -- Now note that my goal would be finished if I could have 
    -- ‖ iteratedFDeriv ℝ n f.toFun x ‖  = ‖ iteratedFDeriv ℝ n (fun x=> !₂[x]) ‖  
    -- Now lean cannot simply apply rw inside arguments of iteratedFDeriv for some reason that I don't understand. So the following is not enough:
    -- have samenumber : ( fun x => f !₂[x] ) x = (f.toFun !₂[x]) := by sorry
    -- So I'll take the more stupid tautological direction:
    have equal_derivative : ‖iteratedFDeriv ℝ n f.toFun (!₂[x] : V 1)‖ = ‖iteratedFDeriv ℝ n (fun x : ℝ => f ( !₂[x] : V 1 )) x‖  := by
     --- Note that the following is a type mismatch
     -- #check (iteratedFDeriv ℝ n f.toFun (!₂[x] : V 1) : V 1)
     --- Indeed. This is not the way Fretchet Derivatives are defined.
     --- I had to learn it on wikipedia! Human understanding ++
     --- LLM tells me that I must try to do something about function compositions
     --- And it's a good idea to do grep with `iteratedFDeriv*comp_right` within mathlib/Analysis/Calculus
     --- So I want to do something like
      -- rw [LinearIsometryEquiv.norm_iteratedFDeriv_comp_right (E : ℝ ≃ₗᵢ[ℝ] V 1)]
      -- Where E is fun x => !₂[x]
      --- But E has to be in ℝ ≃ₗᵢ[ℝ] V 1 
      --- How do I define such an E?
      --- Again I asked LLM and it told me of the following format
      --- I did not know about this notation
      --- Using change again, now I know that it exists
      change ‖iteratedFDeriv ℝ n f (E x)‖ = ‖iteratedFDeriv ℝ n (fun x => f !₂[x]) x‖
      --- Learnt of this step by asking AI
      rw [←LinearIsometryEquiv.norm_iteratedFDeriv_comp_right (E : ℝ ≃ₗᵢ[ℝ] V 1)]
      --- suggested by aesop
      exact enorm_eq_iff_norm_eq.mp rfl
      --- It's done! Can't believe I made it.
    rw [←equal_derivative]
    --- Then lean knows how to finish when I write apply?
    exact RCLike.ofReal_le_ofReal.mp (hC !₂[x])

theorem onedim_comm_fourier (f : Sch 1) : onedim (FourierTransform.fourier f) = FourierTransform.fourier (onedim f) := by
  --- I found this hypothesis by asking AI:
  have h:= Real.fourier_comp_linearIsometry (E : ℝ≃ₗᵢ[ℝ] V 1) f
  --- Must expand E
  simp [E] at h
  --- Must expand onedim
  simp_all [onedim]
  --- Then it was just chasing apply? 
  exact Eq.symm (SchwartzMap.ext h)


-- Let's restate the version for d=1
theorem OneDimPoisson (f : Sch 1 ) : 
  (tsum fun (n : ℤ ) => f (!₂[n])) = (tsum fun (ξ : ℤ ) => Fr 1 f (!₂[ξ]))
    := by
  let g := onedim f
  let Fg := onedim (Fr 1 f) 
  change (tsum fun (n : ℤ ) => g n) = (tsum fun (ξ : ℤ ) => Fg ξ)
  --- I must invoke the one-dim Possion here---
  have poisson := SchwartzMap.tsum_eq_tsum_fourier 
  specialize poisson g 
  specialize poisson 0 
  simp at poisson 
  --- I am almost done, except I must show that Fg is the fourier transform of g
  have Fg_is_fourier : Fg = FourierTransform.fourier g := by
    simp_all only [g, Fg, Fr]
    rw [onedim_comm_fourier f]
  -- once this is okay, I am fine
  rw [Fg_is_fourier]
  exact poisson





----------- FOOLING AROUND -------------

--- This will become Poisson summation eventually

--- Let's define Fourier transform for a one-dimensional function
variable (f : Sch 1)
variable ( a : ℝ )
#check onedim f (1 : ℝ)



--- This is how it works! 
#check ( !₂[a] : V 1 )
#check (!₂[(1 : ℝ)] : V 1) 
#check ( 0 : V 1 )
#check ( ‖(0 :V 1)‖ : ℝ )
      
-- I can call values of a function?
--- f(0)
#check (f 0 : ℂ) 
--- Fr 1 f 0
#check ( Fr 1 f 0 : ℂ )
#check (tsum fun (n : ℤ ) => f (!₂[n]))
#check (tsum fun (n : ℤ ) => Fr 1 f (!₂[n]))

------------ END OF FOOLING AROUND ------------









