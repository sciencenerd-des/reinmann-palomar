/-
Copyright (c) 2026 Biswajit Mondal. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Biswajit Mondal
-/
-- Internal rounding: 38 bits, checked against fixed final error disks.
module

public import XiRectangle.Tile000Gamma
public import XiRectangle.Tile000Zeta
public import Reinmann.RectangleModel
public import XiRectangle.Data

@[expose] public section

/-! Numerical proposals for one closed ball. Every rounding check is proved
by rational arithmetic in the Lean kernel; no native evaluation is used. -/
noncomputable section
namespace Reinmann.XiRectangle.Tile000
open CertifiedTaylorModel CertifiedTaylorComposition RectangleTaylor RectangleModel
open scoped Topology
set_option maxRecDepth 30000
set_option linter.style.longLine false
set_option linter.style.whitespace false

def c : ℂ := Data.centre ⟨0,by norm_num [Data.count]⟩
theorem hc : c ∈ XiAdaptiveTiles.quarter (141/10) := Data.centre_mem_quarter _
theorem hcre : -2<c.re := by linarith [hc.1]

def J_gammaActual : Jet 12 := fun k =>
  match k.val with
  | 0 => ⟨((485564504375/549755813888), (-569952671/68719476736)), (285/274877906944), by norm_num⟩
  | 1 => ⟨((-155370990997/4398046511104), (225433303131/4398046511104)), (3033/1099511627776), by norm_num⟩
  | 2 => ⟨((125155451273/1099511627776), (-34321638331/2199023255552)), (8403/2199023255552), by norm_num⟩
  | 3 => ⟨((-97918026293/4398046511104), (24658532555/2199023255552)), (8085/2199023255552), by norm_num⟩
  | 4 => ⟨((52528895119/4398046511104), (-19836179817/4398046511104)), (48761/17592186044416), by norm_num⟩
  | 5 => ⟨((-260664200165/70368744177664), (73024216701/35184372088832)), (123087/70368744177664), by norm_num⟩
  | 6 => ⟨((24296881243/17592186044416), (-120738449155/140737488355328)), (67875/70368744177664), by norm_num⟩
  | 7 => ⟨((-263983681269/562949953421312), (198973721235/562949953421312)), (8433/17592186044416), by norm_num⟩
  | 8 => ⟨((181611247009/1125899906842624), (-159515514819/1125899906842624)), (247455/1125899906842624), by norm_num⟩
  | 9 => ⟨((-244401247289/4503599627370496), (252198863345/4503599627370496)), (106615/1125899906842624), by norm_num⟩
  | 10 => ⟨((162490346519/9007199254740992), (-49159300323/2251799813685248)), (350383/9007199254740992), by norm_num⟩
  | 11 => ⟨((-212347847327/36028797018963968), (151621325229/18014398509481984)), (138863/9007199254740992), by norm_num⟩
  | 12 => ⟨((34006631819/18014398509481984), (-115764534041/36028797018963968)), (429049/72057594037927936), by norm_num⟩
  | _ => zero
theorem S_gammaActual : Sound J_gammaActual F_gammaActual c := Reinmann.XiRectangle.Tile000Gamma.gammaJet_sound

def J_zetaActual : Jet 12 := fun k =>
  match k.val with
  | 0 => ⟨((117732480645/137438953472), (1022195637/8589934592)), (16573/274877906944), by norm_num⟩
  | 1 => ⟨((18573857949/34359738368), (144492683/4294967296)), (16829/274877906944), by norm_num⟩
  | 2 => ⟨((1313269477/17179869184), (-50614207/17179869184)), (273099/4398046511104), by norm_num⟩
  | 3 => ⟨((-2411589/536870912), (-7085181/17179869184)), (4381869/70368744177664), by norm_num⟩
  | 4 => ⟨((-124859/268435456), (2014833/17179869184)), (17453747/281474976710656), by norm_num⟩
  | 5 => ⟨((3671155/34359738368), (-267629/34359738368)), (138319253/2251799813685248), by norm_num⟩
  | 6 => ⟨((-403/67108864), (-58873/68719476736)), (4384273051/72057594037927936), by norm_num⟩
  | 7 => ⟨((-37471/68719476736), (30147/137438953472)), (34826720467/576460752303423488), by norm_num⟩
  | 8 => ⟨((34241/274877906944), (-601/34359738368)), (138770010953/2305843009213693952), by norm_num⟩
  | 9 => ⟨((-2463/274877906944), (-197/1099511627776)), (138503672649/2305843009213693952), by norm_num⟩
  | 10 => ⟨((-143/2199023255552), (415/2199023255552)), (138404057929/2305843009213693952), by norm_num⟩
  | 11 => ⟨((679/8796093022208), (-181/8796093022208)), (138367619913/2305843009213693952), by norm_num⟩
  | 12 => ⟨((-139/17592186044416), (15/17592186044416)), (138355495753/2305843009213693952), by norm_num⟩
  | _ => zero
theorem S_zetaActual : Sound J_zetaActual F_zetaActual c := Reinmann.XiRectangle.Tile000Zeta.zetaJet_sound

def J_variable : Jet 12 := fun k =>
  match k.val with
  | 0 => ⟨((3/4), (141/640)), 0, by norm_num⟩
  | 1 => ⟨(1, 0), 0, by norm_num⟩
  | 2 => ⟨(0, 0), 0, by norm_num⟩
  | 3 => ⟨(0, 0), 0, by norm_num⟩
  | 4 => ⟨(0, 0), 0, by norm_num⟩
  | 5 => ⟨(0, 0), 0, by norm_num⟩
  | 6 => ⟨(0, 0), 0, by norm_num⟩
  | 7 => ⟨(0, 0), 0, by norm_num⟩
  | 8 => ⟨(0, 0), 0, by norm_num⟩
  | 9 => ⟨(0, 0), 0, by norm_num⟩
  | 10 => ⟨(0, 0), 0, by norm_num⟩
  | 11 => ⟨(0, 0), 0, by norm_num⟩
  | 12 => ⟨(0, 0), 0, by norm_num⟩
  | _ => zero

theorem S_variable : Sound J_variable F_variable c := by
  have h := variable_sound 12 ((3/4), (141/640))
  have he : value ((3/4), (141/640))=c := by norm_num [c,Data.centre,Data.coordinate,value]
  rw [he] at h
  convert h using 1
  all_goals first | (funext k; fin_cases k <;> rfl) | rfl

def J_logpi : Jet 12 := fun k =>
  match k.val with
  | 0 => ⟨((5723649429247/5000000000000), 0), (3/500000000000000), by norm_num⟩
  | 1 => ⟨(0, 0), 0, by norm_num⟩
  | 2 => ⟨(0, 0), 0, by norm_num⟩
  | 3 => ⟨(0, 0), 0, by norm_num⟩
  | 4 => ⟨(0, 0), 0, by norm_num⟩
  | 5 => ⟨(0, 0), 0, by norm_num⟩
  | 6 => ⟨(0, 0), 0, by norm_num⟩
  | 7 => ⟨(0, 0), 0, by norm_num⟩
  | 8 => ⟨(0, 0), 0, by norm_num⟩
  | 9 => ⟨(0, 0), 0, by norm_num⟩
  | 10 => ⟨(0, 0), 0, by norm_num⟩
  | 11 => ⟨(0, 0), 0, by norm_num⟩
  | 12 => ⟨(0, 0), 0, by norm_num⟩
  | _ => zero

theorem S_logpi : Sound J_logpi F_logpi c := by
  have h := constant_sound (d:=12) (c:=c) RectangleLogInputs.logpi_contains
  convert h using 1
  all_goals first | (funext k; fin_cases k <;> rfl) | rfl

def J_negativeHalfLogPi : Jet 12 := fun k =>
  match k.val with
  | 0 => ⟨((-314660955039/549755813888), 0), (1/549755813888), by norm_num⟩
  | 1 => ⟨(0, 0), 0, by norm_num⟩
  | 2 => ⟨(0, 0), 0, by norm_num⟩
  | 3 => ⟨(0, 0), 0, by norm_num⟩
  | 4 => ⟨(0, 0), 0, by norm_num⟩
  | 5 => ⟨(0, 0), 0, by norm_num⟩
  | 6 => ⟨(0, 0), 0, by norm_num⟩
  | 7 => ⟨(0, 0), 0, by norm_num⟩
  | 8 => ⟨(0, 0), 0, by norm_num⟩
  | 9 => ⟨(0, 0), 0, by norm_num⟩
  | 10 => ⟨(0, 0), 0, by norm_num⟩
  | 11 => ⟨(0, 0), 0, by norm_num⟩
  | 12 => ⟨(0, 0), 0, by norm_num⟩
  | _ => zero

set_option maxHeartbeats 5000000 in
theorem S_negativeHalfLogPi : Sound J_negativeHalfLogPi F_negativeHalfLogPi c := by
  apply sound_round (sound_scale (A_logpi hcre) S_logpi)
  intro k
  fin_cases k <;> norm_num [J_negativeHalfLogPi, J_logpi, jetScale, sum, CertifiedTaylorModel.get, CertifiedTaylorModel.mul, CertifiedTaylorModel.add, exact, zero, qmul, qadd, size]

def J_piArg : Jet 12 := fun k =>
  match k.val with
  | 0 => ⟨((-235995716279/549755813888), (-69323741657/549755813888)), (1/274877906944), by norm_num⟩
  | 1 => ⟨((-314660955039/549755813888), 0), (1/549755813888), by norm_num⟩
  | 2 => ⟨(0, 0), 0, by norm_num⟩
  | 3 => ⟨(0, 0), 0, by norm_num⟩
  | 4 => ⟨(0, 0), 0, by norm_num⟩
  | 5 => ⟨(0, 0), 0, by norm_num⟩
  | 6 => ⟨(0, 0), 0, by norm_num⟩
  | 7 => ⟨(0, 0), 0, by norm_num⟩
  | 8 => ⟨(0, 0), 0, by norm_num⟩
  | 9 => ⟨(0, 0), 0, by norm_num⟩
  | 10 => ⟨(0, 0), 0, by norm_num⟩
  | 11 => ⟨(0, 0), 0, by norm_num⟩
  | 12 => ⟨(0, 0), 0, by norm_num⟩
  | _ => zero

set_option maxHeartbeats 5000000 in
theorem S_piArg : Sound J_piArg F_piArg c := by
  apply sound_round (sound_mul (A_negativeHalfLogPi hcre) (A_variable hcre) S_negativeHalfLogPi S_variable)
  intro k
  fin_cases k <;> norm_num [J_piArg, J_negativeHalfLogPi, J_variable, jetMul, sum, CertifiedTaylorModel.get, CertifiedTaylorModel.mul, CertifiedTaylorModel.add, exact, zero, qmul, qadd, size]

def J_piPower : Jet 12 := fun k =>
  match k.val with
  | 0 => ⟨((1454241484991329/2251799813685248), (-46089201754475/562949953421312)), (6123/2251799813685248), by norm_num⟩
  | 1 => ⟨((-203212120253/549755813888), (51523131507/1099511627776)), (1/274877906944), by norm_num⟩
  | 2 => ⟨((232622987221/2199023255552), (-58980068449/4398046511104)), (7/4398046511104), by norm_num⟩
  | 3 => ⟨((-177526990405/8796093022208), (45010831349/17592186044416)), (1/2199023255552), by norm_num⟩
  | 4 => ⟨((101610225731/35184372088832), (-6440655479/17592186044416)), (3/35184372088832), by norm_num⟩
  | 5 => ⟨((-46526504841/140737488355328), (5898248649/140737488355328)), (13/1125899906842624), by norm_num⟩
  | 6 => ⟨((284054829737/9007199254740992), (-9002535337/2251799813685248)), (3/2251799813685248), by norm_num⟩
  | 7 => ⟨((-11613073315/4503599627370496), (11777681427/36028797018963968)), (9/72057594037927936), by norm_num⟩
  | 8 => ⟨((53175328361/288230376151711744), (-26964527831/1152921504606846976)), (23/2305843009213693952), by norm_num⟩
  | 9 => ⟨((-432863200461/36893488147419103232), (1714838937/1152921504606846976)), (13/18446744073709551616), by norm_num⟩
  | 10 => ⟨((198204576821/295147905179352825856), (-50253500943/590295810358705651712)), (27/590295810358705651712), by norm_num⟩
  | 11 => ⟨((-330022840145/9444732965739290427392), (41837588653/9444732965739290427392)), (25/9444732965739290427392), by norm_num⟩
  | 12 => ⟨((125929002709/75557863725914323419136), (-31928492055/151115727451828646838272)), (21/151115727451828646838272), by norm_num⟩
  | _ => zero

def piPowerValuePoly : ℕ → Disk
  | 20 => ⟨(0, 0), 0, by norm_num⟩
  | 19 => ⟨((666937165097003/81129638414606681695789005144064), 0), (1/162259276829213363391578010288128), by norm_num⟩
  | 18 => ⟨((98963536885819/633825300114114700748351602688), (-164258223857/10141204801825835211973625643008)), (3/5070602400912917605986812821504), by norm_num⟩
  | 17 => ⟨((1781308929573127/633825300114114700748351602688), (-97459461297/316912650057057350374175801344)), (7/633825300114114700748351602688), by norm_num⟩
  | 16 => ⟨((1892599262959005/39614081257132168796771975168), (-109637632319/19807040628566084398385987584)), (7/39614081257132168796771975168), by norm_num⟩
  | 15 => ⟨((1892552605649141/2475880078570760549798248448), (-14560609867/154742504910672534362390528)), (1/309485009821345068724781056), by norm_num⟩
  | 14 => ⟨((887109248194849/77371252455336267181195264), (-116479135707/77371252455336267181195264)), (1/19342813113834066795298816), by norm_num⟩
  | 13 => ⟨((1552391615168057/9671406556917033397649408), (-54596543967/2417851639229258349412352)), (7/9671406556917033397649408), by norm_num⟩
  | 12 => ⟨((315317929649333/151115727451828646838272), (-191075701179/604462909807314587353088)), (7/604462909807314587353088), by norm_num⟩
  | 11 => ⟨((945913131184887/37778931862957161709568), (-77618784051/18889465931478580854784)), (5/37778931862957161709568), by norm_num⟩
  | 10 => ⟨((1300564490962793/4722366482869645213696), (-232836335581/4722366482869645213696)), (1/590295810358705651712), by norm_num⟩
  | 9 => ⟨((1625606524863347/590295810358705651712), (-320117437987/590295810358705651712)), (5/295147905179352825856), by norm_num⟩
  | 8 => ⟨((1828671105964739/73786976294838206464), (-400098018437/73786976294838206464)), (13/73786976294838206464), by norm_num⟩
  | 7 => ⟨((914250415901303/4611686018427387904), (-56255401185/1152921504606846976)), (7/4611686018427387904), by norm_num⟩
  | 6 => ⟨((1599746695476811/1152921504606846976), (-449959397791/1152921504606846976)), (7/576460752303423488), by norm_num⟩
  | 5 => ⟨((1199618521854717/144115188075855872), (-393620205385/144115188075855872)), (3/36028797018963968), by norm_num⟩
  | 4 => ⟨((374797025270521/9007199254740992), (-295120911935/18014398509481984)), (9/18014398509481984), by norm_num⟩
  | 3 => ⟨((1498685670856863/9007199254740992), (-368736273773/4503599627370496)), (11/4503599627370496), by norm_num⟩
  | 2 => ⟨((2246772943775019/4503599627370496), (-1473956358345/4503599627370496)), (43/4503599627370496), by norm_num⟩
  | 1 => ⟨((280532919664325/281474976710656), (-552116076341/562949953421312)), (65/2251799813685248), by norm_num⟩
  | 0 => ⟨((279592785818491/281474976710656), (-4407057334593/2251799813685248)), (129/2251799813685248), by norm_num⟩
  | _ => zero

def piPowerValueSquares : ℕ → Disk
  | 0 => ⟨((279592785818491/281474976710656), (-4407057334593/2251799813685248)), (492104537200217/8589934592000000000000000000), by norm_num⟩
  | 1 => ⟨((1110888411099365/1125899906842624), (-8755175695119/2251799813685248)), (257/2251799813685248), by norm_num⟩
  | 2 => ⟨((2192120083036835/2251799813685248), (-17276887861411/2251799813685248)), (255/1125899906842624), by norm_num⟩
  | 3 => ⟨((2133889495148031/2251799813685248), (-33637992705393/2251799813685248)), (501/1125899906842624), by norm_num⟩
  | 4 => ⟨((1010825392933039/1125899906842624), (-63753233156575/2251799813685248)), (965/1125899906842624), by norm_num⟩
  | 5 => ⟨((906609770646719/1125899906842624), (-114474451173845/2251799813685248)), (447/281474976710656), by norm_num⟩
  | 6 => ⟨((1454241484991329/2251799813685248), (-46089201754475/562949953421312)), (6123/2251799813685248), by norm_num⟩
  | _ => zero

def piPowerValue : CertifiedScalarExp.Data :=
  ⟨⟨((-235995716279/549755813888), (-69323741657/549755813888)), (1/274877906944), by norm_num⟩, 0, piPowerValuePoly, piPowerValueSquares⟩

set_option maxHeartbeats 5000000 in
-- A bounded Horner table and six outward-rounded squarings.
theorem piPowerValue_checks : CertifiedScalarExp.Checks piPowerValue := by
  constructor
  · norm_num [piPowerValue, CertifiedScalarExp.reduced, piPowerValuePoly, piPowerValueSquares,
      CertifiedScalarExp.piDisk, CertifiedTaylorModel.mul, CertifiedTaylorModel.add,
      exact, qmul, qadd, size]
  · rfl
  · intro k hk
    interval_cases k <;>
      norm_num [piPowerValue, CertifiedScalarExp.roundingCheck, CertifiedScalarExp.reduced,
        piPowerValuePoly, CertifiedScalarExp.piDisk, CertifiedTaylorModel.mul,
        CertifiedTaylorModel.add, exact, qmul, qadd, size]
  · apply CertifiedScalarExp.disk_ext <;> norm_num [piPowerValue, piPowerValueSquares, piPowerValuePoly, inflate]
  · intro k hk
    interval_cases k <;>
      norm_num [piPowerValue, CertifiedScalarExp.roundingCheck, piPowerValueSquares,
        CertifiedTaylorModel.mul, exact, qmul, qadd, size]

set_option maxHeartbeats 5000000 in
theorem S_piPower : Sound J_piPower F_piPower c := by
  apply exp_sound (A_piArg hcre) S_piArg piPowerValue piPowerValue_checks
  · apply CertifiedScalarExp.disk_ext <;> norm_num [piPowerValue,J_piArg]
  · rfl
  · intro n hn
    have hlt : n < 12 := by omega
    interval_cases n <;> norm_num [J_piPower,J_piArg,sum, CertifiedTaylorModel.get, CertifiedTaylorModel.mul, CertifiedTaylorModel.add, exact, zero, qmul, qadd, size]

def J_piGamma : Jet 12 := fun k =>
  match k.val with
  | 0 => ⟨((313210545795/549755813888), (-42698250347/549755813888)), (417/549755813888), by norm_num⟩
  | 1 => ⟨((-379012516829/1099511627776), (88454989493/1099511627776)), (2687/1099511627776), by norm_num⟩
  | 2 => ⟨((24218404145/137438953472), (-115939567001/2199023255552)), (4459/1099511627776), by norm_num⟩
  | 3 => ⟨((-332751206509/4398046511104), (125304723693/4398046511104)), (10161/2199023255552), by norm_num⟩
  | 4 => ⟨((263969538937/8796093022208), (-120757832561/8796093022208)), (8951/2199023255552), by norm_num⟩
  | 5 => ⟨((-198140363743/17592186044416), (108406913781/17592186044416)), (52109/17592186044416), by norm_num⟩
  | 6 => ⟨((286941854205/70368744177664), (-185590819297/70368744177664)), (65373/35184372088832), by norm_num⟩
  | 7 => ⟨((-202395454903/140737488355328), (9603880363/8796093022208)), (72875/70368744177664), by norm_num⟩
  | 8 => ⟨((34965413833/70368744177664), (-124163580205/281474976710656)), (295483/562949953421312), by norm_num⟩
  | 9 => ⟨((-189884231249/1125899906842624), (196960877755/1125899906842624)), (69353/281474976710656), by norm_num⟩
  | 10 => ⟨((126704269089/2251799813685248), (-4810354737/70368744177664)), (122439/1125899906842624), by norm_num⟩
  | 11 => ⟨((-83018603699/4503599627370496), (59424122483/2251799813685248)), (411599/9007199254740992), by norm_num⟩
  | 12 => ⟨((26631768397/4503599627370496), (-90814903893/9007199254740992)), (41609/2251799813685248), by norm_num⟩
  | _ => zero

set_option maxHeartbeats 5000000 in
theorem S_piGamma : Sound J_piGamma F_piGamma c := by
  apply sound_round (sound_mul (A_piPower hcre) (A_gammaActual hcre) S_piPower S_gammaActual)
  intro k
  fin_cases k <;> norm_num [J_piGamma, J_piPower, J_gammaActual, jetMul, sum, CertifiedTaylorModel.get, CertifiedTaylorModel.mul, CertifiedTaylorModel.add, exact, zero, qmul, qadd, size]

def J_xiProduct : Jet 12 := fun k =>
  match k.val with
  | 0 => ⟨((546764785599/1099511627776), (1391575227/1099511627776)), (10933/274877906944), by norm_num⟩
  | 1 => ⟨((6303178371/1099511627776), (44649981611/8796093022208)), (1197841/17592186044416), by norm_num⟩
  | 2 => ⟨((404485353651/35184372088832), (1436089685/17592186044416)), (1503307/17592186044416), by norm_num⟩
  | 3 => ⟨((69302109043/562949953421312), (246124907763/2251799813685248)), (211768001/2251799813685248), by norm_num⟩
  | 4 => ⟨((139187126009/1125899906842624), (1549384017/1125899906842624)), (217989179/2251799813685248), by norm_num⟩
  | 5 => ⟨((179262149473/144115188075855872), (39889819955/36028797018963968)), (13863461967/144115188075855872), by norm_num⟩
  | 6 => ⟨((480695332015/576460752303423488), (7079403355/576460752303423488)), (13580966893/144115188075855872), by norm_num⟩
  | 7 => ⟨((18324626109/2305843009213693952), (16425464891/2305843009213693952)), (425225657775/4611686018427387904), by norm_num⟩
  | 8 => ⟨((9228956069/2305843009213693952), (252577483/4611686018427387904)), (418148505541/4611686018427387904), by norm_num⟩
  | 9 => ⟨((166494325/4611686018427387904), (191499897/4611686018427387904)), (206828127169/2305843009213693952), by norm_num⟩
  | 10 => ⟨((8378171/576460752303423488), (-9256467/2305843009213693952)), (411152523103/4611686018427387904), by norm_num⟩
  | 11 => ⟨((1136117/4611686018427387904), (4887991/2305843009213693952)), (102470758721/1152921504606846976), by norm_num⟩
  | 12 => ⟨((-12789/288230376151711744), (-4103883/4611686018427387904)), (409285305945/4611686018427387904), by norm_num⟩
  | _ => zero

set_option maxHeartbeats 5000000 in
theorem S_xiProduct : Sound J_xiProduct F_xiProduct c := by
  apply sound_round (sound_mul (A_piGamma hcre) (A_zetaActual hcre) S_piGamma S_zetaActual)
  intro k
  fin_cases k <;> norm_num [J_xiProduct, J_piGamma, J_zetaActual, jetMul, sum, CertifiedTaylorModel.get, CertifiedTaylorModel.mul, CertifiedTaylorModel.add, exact, zero, qmul, qadd, size]

def xiJet : Jet 12 := fun k =>
  match k.val with
  | 0 => ⟨((266974993/536870912), (84935/67108864)), (1/10000000), by norm_num⟩
  | 1 => ⟨((769431/134217728), (5450437/1073741824)), (1/10000000), by norm_num⟩
  | 2 => ⟨((12343913/1073741824), (21913/268435456)), (1/10000000), by norm_num⟩
  | 3 => ⟨((132183/1073741824), (117361/1073741824)), (1/10000000), by norm_num⟩
  | 4 => ⟨((132739/1073741824), (739/536870912)), (1/10000000), by norm_num⟩
  | 5 => ⟨((167/134217728), (1189/1073741824)), (1/10000000), by norm_num⟩
  | 6 => ⟨((895/1073741824), (13/1073741824)), (1/10000000), by norm_num⟩
  | 7 => ⟨((9/1073741824), (1/134217728)), (1/5000000), by norm_num⟩
  | 8 => ⟨((1/268435456), 0), (1/10000000), by norm_num⟩
  | 9 => ⟨(0, 0), (1/10000000), by norm_num⟩
  | 10 => ⟨(0, 0), (1/10000000), by norm_num⟩
  | 11 => ⟨(0, 0), (1/10000000), by norm_num⟩
  | 12 => ⟨(0, 0), (1/10000000), by norm_num⟩
  | _ => zero

set_option maxHeartbeats 5000000 in
theorem xiJet_sound : Sound xiJet xiCompleted c := by
  apply sound_round (xi_sound hc S_xiProduct)
  intro k
  fin_cases k <;> norm_num [xiJet,J_xiProduct,size]

set_option maxHeartbeats 5000000 in
theorem nonzero {z:ℂ} (hz:‖z-Data.centre ⟨0,by norm_num [Data.count]⟩‖≤
    (Data.radius ⟨0,by norm_num [Data.count]⟩:ℝ)) : xiCompleted z≠0 := by
  apply RectangleTileRules.certified_tile_nonzero (a:=xiJet) (c:=c)
    (r:=(174705/524288)) (K:=(30369447/536870912)) (L:=(546766556515/1099511627776)) hc xiJet_sound
  · norm_num
  · norm_num
  · norm_num
  · norm_num [RectangleTileRules.derivativeBudget,xiJet,Finset.sum_range_succ,CertifiedTaylorModel.get,size]
  · norm_num
  · norm_num [xiJet]
  · norm_num [xiJet]
  · simpa only [c,Data.radius] using! hz

end Reinmann.XiRectangle.Tile000
