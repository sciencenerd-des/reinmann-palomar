/-
Copyright (c) 2026 Biswajit Mondal. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Biswajit Mondal
-/
-- Internal rounding: 38 bits, checked against fixed final error disks.
module

public import XiRectangle.Tile004Gamma
public import XiRectangle.Tile004Zeta
public import Reinmann.RectangleModel
public import XiRectangle.Data

@[expose] public section

/-! Numerical proposals for one closed ball. Every rounding check is proved
by rational arithmetic in the Lean kernel; no native evaluation is used. -/
noncomputable section
namespace Reinmann.XiRectangle.Tile004
open CertifiedTaylorModel CertifiedTaylorComposition RectangleTaylor RectangleModel
open scoped Topology
set_option maxRecDepth 30000
set_option linter.style.longLine false
set_option linter.style.whitespace false

def c : ℂ := Data.centre ⟨4,by norm_num [Data.count]⟩
theorem hc : c ∈ XiAdaptiveTiles.quarter (141/10) := Data.centre_mem_quarter _
theorem hcre : -2<c.re := by linarith [hc.1]

def J_gammaActual : Jet 12 := fun k =>
  match k.val with
  | 0 => ⟨((309394306189/549755813888), (7775022607/274877906944)), (925/549755813888), by norm_num⟩
  | 1 => ⟨((73406866187/1099511627776), (259294449257/1099511627776)), (4489/1099511627776), by norm_num⟩
  | 2 => ⟨((-5561242489/1099511627776), (-13438413009/2199023255552)), (43539/8796093022208), by norm_num⟩
  | 3 => ⟨((242513025063/17592186044416), (227723114279/17592186044416)), (18833/4398046511104), by norm_num⟩
  | 4 => ⟨((-285996677359/70368744177664), (50957303361/35184372088832)), (210811/70368744177664), by norm_num⟩
  | 5 => ⟨((142952971339/140737488355328), (-93307704679/140737488355328)), (248955/140737488355328), by norm_num⟩
  | 6 => ⟨((-62433544039/562949953421312), (221074697473/562949953421312)), (504843/562949953421312), by norm_num⟩
  | 7 => ⟨((-82009598559/2251799813685248), (-242028132341/2251799813685248)), (900387/2251799813685248), by norm_num⟩
  | 8 => ⟨((246275781427/9007199254740992), (186027670745/9007199254740992)), (363615/2251799813685248), by norm_num⟩
  | 9 => ⟨((-362824005841/36028797018963968), (-8139973741/36028797018963968)), (2177355/36028797018963968), by norm_num⟩
  | 10 => ⟨((44232307229/18014398509481984), (-29868588839/18014398509481984)), (1536115/72057594037927936), by norm_num⟩
  | 11 => ⟨((-87455857159/288230376151711744), (117944285755/144115188075855872)), (2076403/288230376151711744), by norm_num⟩
  | 12 => ⟨((-19598601651/288230376151711744), (-35706841947/144115188075855872)), (1369965/576460752303423488), by norm_num⟩
  | _ => zero
theorem S_gammaActual : Sound J_gammaActual F_gammaActual c := Reinmann.XiRectangle.Tile004Gamma.gammaJet_sound

def J_zetaActual : Jet 12 := fun k =>
  match k.val with
  | 0 => ⟨((38032811355/68719476736), (1190243019/1073741824)), (16779/274877906944), by norm_num⟩
  | 1 => ⟨((645025485/1073741824), (10859191459/34359738368)), (17389/274877906944), by norm_num⟩
  | 2 => ⟨((2948530683/34359738368), (-1203226089/34359738368)), (286667/4398046511104), by norm_num⟩
  | 3 => ⟨((-152457579/17179869184), (-11163125/4294967296)), (2311767/35184372088832), by norm_num⟩
  | 4 => ⟨((328243/34359738368), (40193391/34359738368)), (18125491/281474976710656), by norm_num⟩
  | 5 => ⟨((4584225/34359738368), (-531129/4294967296)), (70699723/1125899906842624), by norm_num⟩
  | 6 => ⟨((-332789/17179869184), (-69499/68719476736)), (1107864743/18014398509481984), by norm_num⟩
  | 7 => ⟨((71525/68719476736), (127941/68719476736)), (8750720309/144115188075855872), by norm_num⟩
  | 8 => ⟨((21505/274877906944), (-133191/549755813888)), (69523417509/1152921504606846976), by norm_num⟩
  | 9 => ⟨((-23393/1099511627776), (3371/274877906944)), (138606433097/2305843009213693952), by norm_num⟩
  | 10 => ⟨((4517/2199023255552), (397/549755813888)), (138434990921/2305843009213693952), by norm_num⟩
  | 11 => ⟨((-355/4398046511104), (-1709/8796093022208)), (138376532809/2305843009213693952), by norm_num⟩
  | 12 => ⟨((-211/35184372088832), (627/35184372088832)), (138357986121/2305843009213693952), by norm_num⟩
  | _ => zero
theorem S_zetaActual : Sound J_zetaActual F_zetaActual c := Reinmann.XiRectangle.Tile004Zeta.zetaJet_sound

def J_variable : Jet 12 := fun k =>
  match k.val with
  | 0 => ⟨((3/4), (1269/640)), 0, by norm_num⟩
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
  have h := variable_sound 12 ((3/4), (1269/640))
  have he : value ((3/4), (1269/640))=c := by norm_num [c,Data.centre,Data.coordinate,value]
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
  | 0 => ⟨((-29499464535/68719476736), (-311956837457/274877906944)), (3/274877906944), by norm_num⟩
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
  | 0 => ⟨((19341835802257/70368744177664), (-1328804183490373/2251799813685248)), (2263/140737488355328), by norm_num⟩
  | 1 => ⟨((-172977949141/1099511627776), (371367641915/1099511627776)), (13/1099511627776), by norm_num⟩
  | 2 => ⟨((99006513987/2199023255552), (-212557819169/2199023255552)), (9/2199023255552), by norm_num⟩
  | 3 => ⟨((-151114287273/17592186044416), (324428384099/17592186044416)), (1/1099511627776), by norm_num⟩
  | 4 => ⟨((43246260205/35184372088832), (-371382867097/140737488355328)), (11/70368744177664), by norm_num⟩
  | 5 => ⟨((-158416916825/1125899906842624), (340106453647/1125899906842624)), (23/1125899906842624), by norm_num⟩
  | 6 => ⟨((30224096519/2251799813685248), (-259553347907/9007199254740992)), (19/9007199254740992), by norm_num⟩
  | 7 => ⟨((-79082117847/72057594037927936), (169781985327/72057594037927936)), (7/36028797018963968), by norm_num⟩
  | 8 => ⟨((11315957967/144115188075855872), (-194354512683/1152921504606846976)), (9/576460752303423488), by norm_num⟩
  | 9 => ⟨((-11514413575/2305843009213693952), (12360189951/1152921504606846976)), (5/4611686018427387904), by norm_num⟩
  | 10 => ⟨((84357717359/295147905179352825856), (-90554104523/147573952589676412928)), (39/590295810358705651712), by norm_num⟩
  | 11 => ⟨((-140460800237/9444732965739290427392), (75389083443/2361183241434822606848)), (35/9444732965739290427392), by norm_num⟩
  | 12 => ⟨((107193117215/151115727451828646838272), (-115066849179/75557863725914323419136)), (29/151115727451828646838272), by norm_num⟩
  | _ => zero

def piPowerValuePoly : ℕ → Disk
  | 20 => ⟨(0, 0), 0, by norm_num⟩
  | 19 => ⟨((666937165097003/81129638414606681695789005144064), 0), (1/162259276829213363391578010288128), by norm_num⟩
  | 18 => ⟨((1583416590173101/10141204801825835211973625643008), (-739162007357/5070602400912917605986812821504)), (15/10141204801825835211973625643008), by norm_num⟩
  | 17 => ⟨((890653655691927/316912650057057350374175801344), (-1754270303351/633825300114114700748351602688)), (9/316912650057057350374175801344), by norm_num⟩
  | 16 => ⟨((473149335848585/9903520314283042199192993792), (-1973475588315/39614081257132168796771975168)), (5/9903520314283042199192993792), by norm_num⟩
  | 15 => ⟨((236568805783299/309485009821345068724781056), (-131045355885/154742504910672534362390528)), (21/2475880078570760549798248448), by norm_num⟩
  | 14 => ⟨((1774216202196605/154742504910672534362390528), (-524155512597/38685626227668133590597632)), (21/154742504910672534362390528), by norm_num⟩
  | 13 => ⟨((388097330286233/2417851639229258349412352), (-982736520589/4835703278458516698824704)), (5/2417851639229258349412352), by norm_num⟩
  | 12 => ⟨((1261269568131245/604462909807314587353088), (-1719678769225/604462909807314587353088)), (9/302231454903657293676544), by norm_num⟩
  | 11 => ⟨((472955624853829/18889465931478580854784), (-87320983165/2361183241434822606848)), (7/18889465931478580854784), by norm_num⟩
  | 10 => ⟨((162570179237615/590295810358705651712), (-2095522851775/4722366482869645213696)), (21/4722366482869645213696), by norm_num⟩
  | 9 => ⟨((1625601939863145/590295810358705651712), (-2881050169137/590295810358705651712)), (29/590295810358705651712), by norm_num⟩
  | 8 => ⟨((228583100319059/9223372036854775808), (-1800436004283/36893488147419103232)), (9/18446744073709551616), by norm_num⟩
  | 7 => ⟨((1828492953981829/9223372036854775808), (-1012593730445/2305843009213693952)), (5/1152921504606846976), by norm_num⟩
  | 6 => ⟨((1599737834914775/1152921504606846976), (-4049617129959/1152921504606846976)), (5/144115188075855872), by norm_num⟩
  | 5 => ⟨((599804831887853/72057594037927936), (-3542562222895/144115188075855872)), (35/144115188075855872), by norm_num⟩
  | 4 => ⟨((1499172605030907/36028797018963968), (-2656068589173/18014398509481984)), (13/9007199254740992), by norm_num⟩
  | 3 => ⟨((1498662437954991/9007199254740992), (-414824018565/562949953421312)), (65/9007199254740992), by norm_num⟩
  | 2 => ⟨((274257190019/549755813888), (-829087591521/281474976710656)), (65/2251799813685248), by norm_num⟩
  | 1 => ⟨((140259211774651/140737488355328), (-9937832403887/1125899906842624)), (49/562949953421312), by norm_num⟩
  | 0 => ⟨((1118197483333897/1125899906842624), (-9915365754331/562949953421312)), (197/1125899906842624), by norm_num⟩
  | _ => zero

def piPowerValueSquares : ℕ → Disk
  | 0 => ⟨((1118197483333897/1125899906842624), (-9915365754331/562949953421312)), (751499656295421/4294967296000000000000000000), by norm_num⟩
  | 1 => ⟨((138774808735819/140737488355328), (-2461883371125/70368744177664)), (25/70368744177664), by norm_num⟩
  | 2 => ⟨((546668958939195/562949953421312), (-77681623669779/1125899906842624)), (817/1125899906842624), by norm_num⟩
  | 3 => ⟨((264089498717075/281474976710656), (-75435004625505/562949953421312)), (425/281474976710656), by norm_num⟩
  | 4 => ⟨((970894878831863/1125899906842624), (-283102857526811/1125899906842624)), (3647/1125899906842624), by norm_num⟩
  | 5 => ⟨((191511170877699/281474976710656), (-488254973439423/1125899906842624)), (8125/1125899906842624), by norm_num⟩
  | 6 => ⟨((19341835802257/70368744177664), (-1328804183490373/2251799813685248)), (2263/140737488355328), by norm_num⟩
  | _ => zero

def piPowerValue : CertifiedScalarExp.Data :=
  ⟨⟨((-29499464535/68719476736), (-311956837457/274877906944)), (3/274877906944), by norm_num⟩, 0, piPowerValuePoly, piPowerValueSquares⟩

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
  | 0 => ⟨((94217562163/549755813888), (-89150891765/274877906944)), (403/274877906944), by norm_num⟩
  | 1 => ⟨((65334872163/1099511627776), (116030072493/549755813888)), (4813/1099511627776), by norm_num⟩
  | 2 => ⟨((-73754857399/1099511627776), (-145952547487/2199023255552)), (14399/2199023255552), by norm_num⟩
  | 3 => ⟨((305511226131/8796093022208), (78955963291/8796093022208)), (59645/8796093022208), by norm_num⟩
  | 4 => ⟨((-414397157443/35184372088832), (59548924641/17592186044416)), (48645/8796093022208), by norm_num⟩
  | 5 => ⟨((188788314071/70368744177664), (-101787213031/35184372088832)), (132665/35184372088832), by norm_num⟩
  | 6 => ⟨((-64554362637/281474976710656), (337442553043/281474976710656)), (622839/281474976710656), by norm_num⟩
  | 7 => ⟨((-155499592423/1125899906842624), (-96071237447/281474976710656)), (80249/70368744177664), by norm_num⟩
  | 8 => ⟨((203462223311/2251799813685248), (17365793149/281474976710656)), (1184949/2251799813685248), by norm_num⟩
  | 9 => ⟨((-290427000893/9007199254740992), (-120987011/9007199254740992)), (997463/4503599627370496), by norm_num⟩
  | 10 => ⟨((17505950861/2251799813685248), (-194628041047/36028797018963968)), (3114377/36028797018963968), by norm_num⟩
  | 11 => ⟨((-68457325959/72057594037927936), (375974577835/144115188075855872)), (571827/18014398509481984), by norm_num⟩
  | 12 => ⟨((-62532542737/288230376151711744), (-226304076717/288230376151711744)), (3205883/288230376151711744), by norm_num⟩
  | _ => zero

set_option maxHeartbeats 5000000 in
theorem S_piGamma : Sound J_piGamma F_piGamma c := by
  apply sound_round (sound_mul (A_piPower hcre) (A_gammaActual hcre) S_piPower S_gammaActual)
  intro k
  fin_cases k <;> norm_num [J_piGamma, J_piPower, J_gammaActual, jetMul, sum, CertifiedTaylorModel.get, CertifiedTaylorModel.mul, CertifiedTaylorModel.add, exact, zero, qmul, qadd, size]

def J_xiProduct : Jet 12 := fun k =>
  match k.val with
  | 0 => ⟨((499584588917/1099511627776), (2879509871/274877906944)), (17975/549755813888), by norm_num⟩
  | 1 => ⟨((38570845607/8796093022208), (5773743489/137438953472)), (31055/549755813888), by norm_num⟩
  | 2 => ⟨((154629001621/17592186044416), (22633888241/35184372088832)), (2555793/35184372088832), by norm_num⟩
  | 3 => ⟨((5533829969/70368744177664), (484798747089/562949953421312)), (44545493/562949953421312), by norm_num⟩
  | 4 => ⟨((355398649935/4503599627370496), (46673192063/4503599627370496)), (352778203/4503599627370496), by norm_num⟩
  | 5 => ⟨((23726726127/36028797018963968), (300299787871/36028797018963968)), (2655264307/36028797018963968), by norm_num⟩
  | 6 => ⟨((127103732469/288230376151711744), (12828109961/144115188075855872)), (4918136547/72057594037927936), by norm_num⟩
  | 7 => ⟨((7950708281/2305843009213693952), (235672213367/4611686018427387904)), (147252077321/2305843009213693952), by norm_num⟩
  | 8 => ⟨((3987364505/2305843009213693952), (304573015/576460752303423488)), (70307639563/1152921504606846976), by norm_num⟩
  | 9 => ⟨((50413233/4611686018427387904), (1962946551/9223372036854775808)), (547562557553/9223372036854775808), by norm_num⟩
  | 10 => ⟨((31490643/4611686018427387904), (66021401/9223372036854775808)), (540183587627/9223372036854775808), by norm_num⟩
  | 11 => ⟨((-2518629/2305843009213693952), (-2404989/2305843009213693952)), (536878989401/9223372036854775808), by norm_num⟩
  | 12 => ⟨((2586031/4611686018427387904), (4934735/9223372036854775808)), (535516044301/9223372036854775808), by norm_num⟩
  | _ => zero

set_option maxHeartbeats 5000000 in
theorem S_xiProduct : Sound J_xiProduct F_xiProduct c := by
  apply sound_round (sound_mul (A_piGamma hcre) (A_zetaActual hcre) S_piGamma S_zetaActual)
  intro k
  fin_cases k <;> norm_num [J_xiProduct, J_piGamma, J_zetaActual, jetMul, sum, CertifiedTaylorModel.get, CertifiedTaylorModel.mul, CertifiedTaylorModel.add, exact, zero, qmul, qadd, size]

def xiJet : Jet 12 := fun k =>
  match k.val with
  | 0 => ⟨((487875575/1073741824), (11248085/1073741824)), (1/10000000), by norm_num⟩
  | 1 => ⟨((4708355/1073741824), (45107371/1073741824)), (1/10000000), by norm_num⟩
  | 2 => ⟨((9437805/1073741824), (690731/1073741824)), (1/10000000), by norm_num⟩
  | 3 => ⟨((84439/1073741824), (115585/134217728)), (1/10000000), by norm_num⟩
  | 4 => ⟨((42367/536870912), (1391/134217728)), (1/10000000), by norm_num⟩
  | 5 => ⟨((707/1073741824), (4475/536870912)), (1/10000000), by norm_num⟩
  | 6 => ⟨((237/536870912), (95/1073741824)), (1/10000000), by norm_num⟩
  | 7 => ⟨((1/268435456), (55/1073741824)), (1/10000000), by norm_num⟩
  | 8 => ⟨((1/536870912), (1/1073741824)), (1/10000000), by norm_num⟩
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
theorem nonzero {z:ℂ} (hz:‖z-Data.centre ⟨4,by norm_num [Data.count]⟩‖≤
    (Data.radius ⟨4,by norm_num [Data.count]⟩:ℝ)) : xiCompleted z≠0 := by
  apply RectangleTileRules.certified_tile_nonzero (a:=xiJet) (c:=c)
    (r:=(174705/524288)) (K:=(24415417/268435456)) (L:=(62464668337/137438953472)) hc xiJet_sound
  · norm_num
  · norm_num
  · norm_num
  · norm_num [RectangleTileRules.derivativeBudget,xiJet,Finset.sum_range_succ,CertifiedTaylorModel.get,size]
  · norm_num
  · norm_num [xiJet]
  · norm_num [xiJet]
  · simpa only [c,Data.radius] using! hz

end Reinmann.XiRectangle.Tile004
