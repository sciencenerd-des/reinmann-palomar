/-
Copyright (c) 2026 Biswajit Mondal. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Biswajit Mondal
-/
module

public import XiRectangle.Tile000
public import XiRectangle.Tile001
public import XiRectangle.Tile002
public import XiRectangle.Tile003
public import XiRectangle.Tile004
public import XiRectangle.Tile005
public import XiRectangle.Tile006
public import XiRectangle.Tile007
public import XiRectangle.Tile008
public import XiRectangle.Tile009
public import XiRectangle.Tile010
public import XiRectangle.Tile011
public import XiRectangle.Tile012
public import XiRectangle.Tile013
public import XiRectangle.Tile014
public import XiRectangle.Tile015
public import XiRectangle.Tile016
public import XiRectangle.Tile017
public import XiRectangle.Tile018
public import XiRectangle.Tile019
public import XiRectangle.Tile020
public import XiRectangle.Tile021
public import XiRectangle.Tile022
public import XiRectangle.Tile023
public import XiRectangle.Tile024
public import XiRectangle.Tile025
public import XiRectangle.Tile026
public import XiRectangle.Tile027
public import XiRectangle.Tile028
public import XiRectangle.Tile029
public import XiRectangle.Tile030
public import XiRectangle.Tile031
public import XiRectangle.Tile032
public import XiRectangle.Tile033
public import XiRectangle.Tile034
public import XiRectangle.Tile035
public import XiRectangle.Tile036
public import XiRectangle.Tile037
public import XiRectangle.Tile038
public import XiRectangle.Tile039
public import XiRectangle.Tile040
public import XiRectangle.Tile041
public import XiRectangle.Tile042
public import XiRectangle.Tile043
public import XiRectangle.Cover
public import Reinmann.QuasiRHInputs
public import Reinmann.XiAnnihilator

@[expose] public section

/-! A finite certificate for actual Xi on a closed rectangle. This does not
assert the Riemann hypothesis, nor all-order Pólya-frequency positivity. -/
noncomputable section
namespace Reinmann.XiRectangle

theorem all_tiles_nonzero (i:Fin Data.count) {z:ℂ}
    (hz:‖z-Data.centre i‖≤(Data.radius i:ℝ)) : xiCompleted z≠0 := by
  fin_cases i
  · exact Tile000.nonzero hz
  · exact Tile001.nonzero hz
  · exact Tile002.nonzero hz
  · exact Tile003.nonzero hz
  · exact Tile004.nonzero hz
  · exact Tile005.nonzero hz
  · exact Tile006.nonzero hz
  · exact Tile007.nonzero hz
  · exact Tile008.nonzero hz
  · exact Tile009.nonzero hz
  · exact Tile010.nonzero hz
  · exact Tile011.nonzero hz
  · exact Tile012.nonzero hz
  · exact Tile013.nonzero hz
  · exact Tile014.nonzero hz
  · exact Tile015.nonzero hz
  · exact Tile016.nonzero hz
  · exact Tile017.nonzero hz
  · exact Tile018.nonzero hz
  · exact Tile019.nonzero hz
  · exact Tile020.nonzero hz
  · exact Tile021.nonzero hz
  · exact Tile022.nonzero hz
  · exact Tile023.nonzero hz
  · exact Tile024.nonzero hz
  · exact Tile025.nonzero hz
  · exact Tile026.nonzero hz
  · exact Tile027.nonzero hz
  · exact Tile028.nonzero hz
  · exact Tile029.nonzero hz
  · exact Tile030.nonzero hz
  · exact Tile031.nonzero hz
  · exact Tile032.nonzero hz
  · exact Tile033.nonzero hz
  · exact Tile034.nonzero hz
  · exact Tile035.nonzero hz
  · exact Tile036.nonzero hz
  · exact Tile037.nonzero hz
  · exact Tile038.nonzero hz
  · exact Tile039.nonzero hz
  · exact Tile040.nonzero hz
  · exact Tile041.nonzero hz
  · exact Tile042.nonzero hz
  · exact Tile043.nonzero hz

theorem quarter_nonzero : ∀ z ∈ XiAdaptiveTiles.quarter (141/10), xiCompleted z≠0 := by
  intro z hz
  obtain ⟨i,hi⟩ := Cover.quarter_covered z hz
  exact all_tiles_nonzero i hi

theorem rectangle_nonzero {z:ℂ} (hx0:0≤z.re) (hx1:z.re≤1)
    (hy:|z.im|≤(141/10:ℝ)) : xiCompleted z≠0 :=
  XiAdaptiveTiles.xi_rectangle_nonzero_of_quarter quarter_nonzero hx0 hx1 hy

theorem zetaNoLowStripZero : ZetaNoLowStripZero (141/10) := by
  intro s hs
  by_contra h
  have hxi := rectangle_nonzero hs.2.1.le hs.2.2.le (not_le.mp h).le
  exact hxi (XiAnnihilator.xi_zero_of_strip_zero hs.1 hs.2.1 hs.2.2)

/-- The sector bridge remains an explicit classical input. -/
theorem finitePF43 (hB:KatkovaSectorBridge 43) : FinitePF XiMomentCoeff 43 :=
  xi_finitePF43_of_classical zetaNoLowStripZero hB

theorem finitePF58 (hq:QuasiRiemannHypothesisSevenEighths) (hB:KatkovaSectorBridge 58) :
    FinitePF XiMomentCoeff 58 := xi_finitePF58_of_quasiRH hq zetaNoLowStripZero hB

end Reinmann.XiRectangle
