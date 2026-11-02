/-
Copyright (c) 2026 Biswajit Mondal. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Biswajit Mondal
-/
-- Internal rounding: 30 bits, checked against fixed final error disks.
module

public import Reinmann.RectangleModel
public import XiRectangle.Data

@[expose] public section

/-! Numerical proposals for one closed ball. Every rounding check is proved
by rational arithmetic in the Lean kernel; no native evaluation is used. -/
noncomputable section
namespace Reinmann.XiRectangle.Tile037Terms3
open CertifiedTaylorModel CertifiedTaylorComposition RectangleTaylor RectangleModel
open scoped Topology
set_option maxRecDepth 30000
set_option linter.style.longLine false
set_option linter.style.whitespace false

def c : ℂ := Data.centre ⟨37,by norm_num [Data.count]⟩
theorem hc : c ∈ XiAdaptiveTiles.quarter (141/10) := Data.centre_mem_quarter _
theorem hcre : -2<c.re := by linarith [hc.1]

def J_variable : Jet 12 := fun k =>
  match k.val with
  | 0 => ⟨((5/8), (3525/256)), 0, by norm_num⟩
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
  have h := variable_sound 12 ((5/8), (3525/256))
  have he : value ((5/8), (3525/256))=c := by norm_num [c,Data.centre,Data.coordinate,value]
  rw [he] at h
  convert h using 1
  all_goals first | (funext k; fin_cases k <;> rfl) | rfl

def J_log22 : Jet 12 := fun k =>
  match k.val with
  | 0 => ⟨((772760613339579/250000000000000), 0), (1/125000000000000), by norm_num⟩
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

theorem S_log22 : Sound J_log22 F_log22 c := by
  have h := constant_sound (d:=12) (c:=c) RectangleLogInputs.log22_contains
  convert h using 1
  all_goals first | (funext k; fin_cases k <;> rfl) | rfl

def J_negLog22 : Jet 12 := fun k =>
  match k.val with
  | 0 => ⟨((-1659490781/536870912), 0), (1/536870912), by norm_num⟩
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
theorem S_negLog22 : Sound J_negLog22 F_negLog22 c := by
  apply sound_round (sound_scale (A_log22 hcre) S_log22)
  intro k
  fin_cases k <;> norm_num [J_negLog22, J_log22, jetScale, sum, CertifiedTaylorModel.get, CertifiedTaylorModel.mul, CertifiedTaylorModel.add, exact, zero, qmul, qadd, size]

def J_arg22 : Jet 12 := fun k =>
  match k.val with
  | 0 => ⟨((-64823859/33554432), (-357037659/8388608)), (1/16777216), by norm_num⟩
  | 1 => ⟨((-1659490781/536870912), 0), (1/536870912), by norm_num⟩
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
theorem S_arg22 : Sound J_arg22 F_arg22 c := by
  apply sound_round (sound_mul (A_negLog22 hcre) (A_variable hcre) S_negLog22 S_variable)
  intro k
  fin_cases k <;> norm_num [J_arg22, J_negLog22, J_variable, jetMul, sum, CertifiedTaylorModel.get, CertifiedTaylorModel.mul, CertifiedTaylorModel.add, exact, zero, qmul, qadd, size]

def J_term22 : Jet 12 := fun k =>
  match k.val with
  | 0 => ⟨((195910459512303/9007199254740992), (20157886514441/140737488355328)), (49861831/2251799813685248), by norm_num⟩
  | 1 => ⟨((-72189277/1073741824), (-475379051/1073741824)), (149/2147483648), by norm_num⟩
  | 2 => ⟨((27892515/268435456), (367354207/536870912)), (29/268435456), by norm_num⟩
  | 3 => ⟨((-229911861/2147483648), (-378502483/536870912)), (241/2147483648), by norm_num⟩
  | 4 => ⟨((177666831/2147483648), (292491811/536870912)), (47/536870912), by norm_num⟩
  | 5 => ⟨((-219670287/4294967296), (-180820921/536870912)), (117/2147483648), by norm_num⟩
  | 6 => ⟨((28292091/1073741824), (1490467049/8589934592)), (243/8589934592), by norm_num⟩
  | 7 => ⟨((-99945205/8589934592), (-1316313407/17179869184)), (27/2147483648), by norm_num⟩
  | 8 => ⟨((38616859/8589934592), (254298789/8589934592)), (169/34359738368), by norm_num⟩
  | 9 => ⟨((-212206845/137438953472), (-698709647/68719476736)), (235/137438953472), by norm_num⟩
  | 10 => ⟨((262376147/549755813888), (1727792945/549755813888)), (293/549755813888), by norm_num⟩
  | 11 => ⟨((-36864355/274877906944), (-242758243/274877906944)), (83/549755813888), by norm_num⟩
  | 12 => ⟨((75966191/2199023255552), (250125345/1099511627776)), (173/4398046511104), by norm_num⟩
  | _ => zero

def term22ValuePoly : ℕ → Disk
  | 20 => ⟨(0, 0), 0, by norm_num⟩
  | 19 => ⟨((666937165097003/81129638414606681695789005144064), 0), (1/162259276829213363391578010288128), by norm_num⟩
  | 18 => ⟨((1581459249645961/10141204801825835211973625643008), (1849827704123/10141204801825835211973625643008)), (77643/10141204801825835211973625643008), by norm_num⟩
  | 17 => ⟨((1778986555873195/633825300114114700748351602688), (1094845272567/316912650057057350374175801344)), (361/2475880078570760549798248448), by norm_num⟩
  | 16 => ⟨((1889986721192839/39614081257132168796771975168), (2462981817299/39614081257132168796771975168)), (51991/19807040628566084398385987584), by norm_num⟩
  | 15 => ⟨((472444231692397/618970019642690137449562112), (654100536599/618970019642690137449562112)), (3453/77371252455336267181195264), by norm_num⟩
  | 14 => ⟨((1771442982675551/154742504910672534362390528), (2615821755533/154742504910672534362390528)), (110515/154742504910672534362390528), by norm_num⟩
  | 13 => ⟨((1549789746600719/9671406556917033397649408), (2451716380233/9671406556917033397649408)), (103627/9671406556917033397649408), by norm_num⟩
  | 12 => ⟨((157374407399811/75557863725914323419136), (2144635485515/604462909807314587353088)), (22673/151115727451828646838272), by norm_num⟩
  | 11 => ⟨((944063672607519/37778931862957161709568), (870969342683/18889465931478580854784)), (147411/75557863725914323419136), by norm_num⟩
  | 10 => ⟨((648895295708439/2361183241434822606848), (2611897504133/4722366482869645213696)), (55295/2361183241434822606848), by norm_num⟩
  | 9 => ⟨((1621792881737915/590295810358705651712), (897429409311/147573952589676412928)), (9507/36893488147419103232), by norm_num⟩
  | 8 => ⟨((455976188896293/18446744073709551616), (4484686073005/73786976294838206464)), (23777/9223372036854775808), by norm_num⟩
  | 7 => ⟨((1823139655627629/9223372036854775808), (2520944949343/4611686018427387904)), (214099/9223372036854775808), by norm_num⟩
  | 6 => ⟨((797193365140381/576460752303423488), (5037665338411/1152921504606846976)), (214231/1152921504606846976), by norm_num⟩
  | 5 => ⟨((1194929915999107/144115188075855872), (4403208466503/144115188075855872)), (187601/144115188075855872), by norm_num⟩
  | 4 => ⟨((746078961510499/18014398509481984), (3297662549361/18014398509481984)), (281699/36028797018963968), by norm_num⟩
  | 3 => ⟨((744951367268443/4503599627370496), (4113787561637/4503599627370496)), (352645/9007199254740992), by norm_num⟩
  | 2 => ⟨((2229221459754981/4503599627370496), (8202747309639/2251799813685248)), (706857/4503599627370496), by norm_num⟩
  | 1 => ⟨((2217972206780085/2251799813685248), (24484410915365/2251799813685248)), (532107/1125899906842624), by norm_num⟩
  | 0 => ⟨((2184304906890723/2251799813685248), (48475343093973/2251799813685248)), (2144189/2251799813685248), by norm_num⟩
  | _ => zero

def term22ValueSquares : ℕ → Disk
  | 0 => ⟨((2184304906890723/2251799813685248), (48475343093973/2251799813685248)), (8179431923873137717/8589934592000000000000000000), by norm_num⟩
  | 1 => ⟨((529447382311289/562949953421312), (47022354802529/1125899906842624)), (4252157/2251799813685248), by norm_num⟩
  | 2 => ⟨((248478353602517/281474976710656), (22111967954707/281474976710656)), (4176689/1125899906842624), by norm_num⟩
  | 3 => ⟨((870451132786165/1125899906842624), (312317376500301/2251799813685248)), (16060705/2251799813685248), by norm_num⟩
  | 4 => ⟨((651300914225237/1125899906842624), (482915066448247/2251799813685248)), (14644355/1125899906842624), by norm_num⟩
  | 5 => ⟨((649953229938573/2251799813685248), (139676281328109/562949953421312)), (11611931/562949953421312), by norm_num⟩
  | 6 => ⟨((195910459512303/9007199254740992), (20157886514441/140737488355328)), (49861831/2251799813685248), by norm_num⟩
  | _ => zero

def term22Value : CertifiedScalarExp.Data :=
  ⟨⟨((-64823859/33554432), (-357037659/8388608)), (1/16777216), by norm_num⟩, -7, term22ValuePoly, term22ValueSquares⟩

set_option maxHeartbeats 5000000 in
-- A bounded Horner table and six outward-rounded squarings.
theorem term22Value_checks : CertifiedScalarExp.Checks term22Value := by
  constructor
  · norm_num [term22Value, CertifiedScalarExp.reduced, term22ValuePoly, term22ValueSquares,
      CertifiedScalarExp.piDisk, CertifiedTaylorModel.mul, CertifiedTaylorModel.add,
      exact, qmul, qadd, size]
  · rfl
  · intro k hk
    interval_cases k <;>
      norm_num [term22Value, CertifiedScalarExp.roundingCheck, CertifiedScalarExp.reduced,
        term22ValuePoly, CertifiedScalarExp.piDisk, CertifiedTaylorModel.mul,
        CertifiedTaylorModel.add, exact, qmul, qadd, size]
  · apply CertifiedScalarExp.disk_ext <;> norm_num [term22Value, term22ValueSquares, term22ValuePoly, inflate]
  · intro k hk
    interval_cases k <;>
      norm_num [term22Value, CertifiedScalarExp.roundingCheck, term22ValueSquares,
        CertifiedTaylorModel.mul, exact, qmul, qadd, size]

set_option maxHeartbeats 5000000 in
theorem S_term22 : Sound J_term22 F_term22 c := by
  apply exp_sound (A_arg22 hcre) S_arg22 term22Value term22Value_checks
  · apply CertifiedScalarExp.disk_ext <;> norm_num [term22Value,J_arg22]
  · rfl
  · intro n hn
    have hlt : n < 12 := by omega
    interval_cases n <;> norm_num [J_term22,J_arg22,sum, CertifiedTaylorModel.get, CertifiedTaylorModel.mul, CertifiedTaylorModel.add, exact, zero, qmul, qadd, size]

def J_log23 : Jet 12 := fun k =>
  match k.val with
  | 0 => ⟨((62709884318583/20000000000000), 0), (1/125000000000000), by norm_num⟩
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

theorem S_log23 : Sound J_log23 F_log23 c := by
  have h := constant_sound (d:=12) (c:=c) RectangleLogInputs.log23_contains
  convert h using 1
  all_goals first | (funext k; fin_cases k <;> rfl) | rfl

def J_negLog23 : Jet 12 := fun k =>
  match k.val with
  | 0 => ⟨((-1683355639/536870912), 0), (1/536870912), by norm_num⟩
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
theorem S_negLog23 : Sound J_negLog23 F_negLog23 c := by
  apply sound_round (sound_scale (A_log23 hcre) S_log23)
  intro k
  fin_cases k <;> norm_num [J_negLog23, J_log23, jetScale, sum, CertifiedTaylorModel.get, CertifiedTaylorModel.mul, CertifiedTaylorModel.add, exact, zero, qmul, qadd, size]

def J_arg23 : Jet 12 := fun k =>
  match k.val with
  | 0 => ⟨((-4109755/2097152), (-724344315/16777216)), (1/16777216), by norm_num⟩
  | 1 => ⟨((-1683355639/536870912), 0), (1/536870912), by norm_num⟩
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
theorem S_arg23 : Sound J_arg23 F_arg23 c := by
  apply sound_round (sound_mul (A_negLog23 hcre) (A_variable hcre) S_negLog23 S_variable)
  intro k
  fin_cases k <;> norm_num [J_arg23, J_negLog23, J_variable, jetMul, sum, CertifiedTaylorModel.get, CertifiedTaylorModel.mul, CertifiedTaylorModel.add, exact, zero, qmul, qadd, size]

def J_term23 : Jet 12 := fun k =>
  match k.val with
  | 0 => ⟨((219224201619101/2251799813685248), (458740346907131/4503599627370496)), (146020475/9007199254740992), by norm_num⟩
  | 1 => ⟨((-655533043/2147483648), (-685871937/2147483648)), (111/2147483648), by norm_num⟩
  | 2 => ⟨((64231877/134217728), (1075273745/2147483648)), (11/134217728), by norm_num⟩
  | 3 => ⟨((-537063143/1073741824), (-561919101/1073741824)), (47/536870912), by norm_num⟩
  | 4 => ⟨((841979189/2147483648), (880947045/2147483648)), (149/2147483648), by norm_num⟩
  | 5 => ⟨((-528004175/2147483648), (-552440873/2147483648)), (95/2147483648), by norm_num⟩
  | 6 => ⟨((551851345/4294967296), (577391721/4294967296)), (101/4294967296), by norm_num⟩
  | 7 => ⟨((-494379057/8589934592), (-517259543/8589934592)), (183/17179869184), by norm_num⟩
  | 8 => ⟨((775061337/34359738368), (101366519/4294967296)), (73/17179869184), by norm_num⟩
  | 9 => ⟨((-67505565/8589934592), (-141259615/17179869184)), (13/8589934592), by norm_num⟩
  | 10 => ⟨((677322587/274877906944), (708669929/274877906944)), (33/68719476736), by norm_num⟩
  | 11 => ⟨((-386134737/549755813888), (-808011077/1099511627776)), (19/137438953472), by norm_num⟩
  | 12 => ⟨((807148823/4398046511104), (422252343/2199023255552)), (161/4398046511104), by norm_num⟩
  | _ => zero

def term23ValuePoly : ℕ → Disk
  | 20 => ⟨(0, 0), 0, by norm_num⟩
  | 19 => ⟨((666937165097003/81129638414606681695789005144064), 0), (1/162259276829213363391578010288128), by norm_num⟩
  | 18 => ⟨((395355765008039/2535301200456458802993406410752), (1052525271349/10141204801825835211973625643008)), (77643/10141204801825835211973625643008), by norm_num⟩
  | 17 => ⟨((1778945453076867/633825300114114700748351602688), (311461302811/158456325028528675187087900672)), (92323/633825300114114700748351602688), by norm_num⟩
  | 16 => ⟨((944970293713369/19807040628566084398385987584), (1401334987503/39614081257132168796771975168)), (103871/39614081257132168796771975168), by norm_num⟩
  | 15 => ⟨((1889728047373263/2475880078570760549798248448), (744310384769/1237940039285380274899124224)), (110373/2475880078570760549798248448), by norm_num⟩
  | 14 => ⟨((442848564528823/38685626227668133590597632), (5813617251/604462909807314587353088)), (55191/77371252455336267181195264), by norm_num⟩
  | 13 => ⟨((1549744231745529/9671406556917033397649408), (43591017671/302231454903657293676544)), (103495/9671406556917033397649408), by norm_num⟩
  | 12 => ⟨((1258955598015301/604462909807314587353088), (76262064575/37778931862957161709568)), (90569/604462909807314587353088), by norm_num⟩
  | 11 => ⟨((1888063203660279/75557863725914323419136), (1982147428895/75557863725914323419136)), (147195/75557863725914323419136), by norm_num⟩
  | 10 => ⟨((1297742754412465/4722366482869645213696), (743013921599/2361183241434822606848)), (55207/2361183241434822606848), by norm_num⟩
  | 9 => ⟨((405431885706779/147573952589676412928), (1021170900519/295147905179352825856)), (18981/73786976294838206464), by norm_num⟩
  | 8 => ⟨((1823823736672129/73786976294838206464), (1275754157035/36893488147419103232)), (189853/73786976294838206464), by norm_num⟩
  | 7 => ⟨((1823049408412813/9223372036854775808), (1434248547039/4611686018427387904)), (213645/9223372036854775808), by norm_num⟩
  | 6 => ⟨((99643600319873/72057594037927936), (2866061812845/1152921504606846976)), (213721/1152921504606846976), by norm_num⟩
  | 5 => ⟨((298713297837799/36028797018963968), (626266757429/36028797018963968)), (187091/144115188075855872), by norm_num⟩
  | 4 => ⟨((1492045349699421/36028797018963968), (938033253059/9007199254740992)), (140403/18014398509481984), by norm_num⟩
  | 3 => ⟨((744883201548543/4503599627370496), (4680612872581/9007199254740992)), (43913/1125899906842624), by norm_num⟩
  | 2 => ⟨((2228961897927951/4503599627370496), (9332624634009/4503599627370496)), (703503/4503599627370496), by norm_num⟩
  | 1 => ⟨((554403856540899/562949953421312), (6963820254915/1125899906842624)), (264375/562949953421312), by norm_num⟩
  | 0 => ⟨((2183720455392549/2251799813685248), (3446416262309/281474976710656)), (2124019/2251799813685248), by norm_num⟩
  | _ => zero

def term23ValueSquares : ℕ → Disk
  | 0 => ⟨((2183720455392549/2251799813685248), (3446416262309/281474976710656)), (8102489480025481467/8589934592000000000000000000), by norm_num⟩
  | 1 => ⟨((1058680887190731/1125899906842624), (53475515143487/2251799813685248)), (1042905/562949953421312), by norm_num⟩
  | 2 => ⟨((1989680088639623/2251799813685248), (50282894128529/1125899906842624)), (31419/8796093022208), by norm_num⟩
  | 3 => ⟨((876790501838357/1125899906842624), (11107434222025/140737488355328)), (14932411/2251799813685248), by norm_num⟩
  | 4 => ⟨((1351568773405231/2251799813685248), (276795982064921/2251799813685248)), (25614147/2251799813685248), by norm_num⟩
  | 5 => ⟨((1554420710864723/4503599627370496), (166137684038051/1125899906842624)), (74090379/4503599627370496), by norm_num⟩
  | 6 => ⟨((219224201619101/2251799813685248), (458740346907131/4503599627370496)), (146020475/9007199254740992), by norm_num⟩
  | _ => zero

def term23Value : CertifiedScalarExp.Data :=
  ⟨⟨((-4109755/2097152), (-724344315/16777216)), (1/16777216), by norm_num⟩, -7, term23ValuePoly, term23ValueSquares⟩

set_option maxHeartbeats 5000000 in
-- A bounded Horner table and six outward-rounded squarings.
theorem term23Value_checks : CertifiedScalarExp.Checks term23Value := by
  constructor
  · norm_num [term23Value, CertifiedScalarExp.reduced, term23ValuePoly, term23ValueSquares,
      CertifiedScalarExp.piDisk, CertifiedTaylorModel.mul, CertifiedTaylorModel.add,
      exact, qmul, qadd, size]
  · rfl
  · intro k hk
    interval_cases k <;>
      norm_num [term23Value, CertifiedScalarExp.roundingCheck, CertifiedScalarExp.reduced,
        term23ValuePoly, CertifiedScalarExp.piDisk, CertifiedTaylorModel.mul,
        CertifiedTaylorModel.add, exact, qmul, qadd, size]
  · apply CertifiedScalarExp.disk_ext <;> norm_num [term23Value, term23ValueSquares, term23ValuePoly, inflate]
  · intro k hk
    interval_cases k <;>
      norm_num [term23Value, CertifiedScalarExp.roundingCheck, term23ValueSquares,
        CertifiedTaylorModel.mul, exact, qmul, qadd, size]

set_option maxHeartbeats 5000000 in
theorem S_term23 : Sound J_term23 F_term23 c := by
  apply exp_sound (A_arg23 hcre) S_arg23 term23Value term23Value_checks
  · apply CertifiedScalarExp.disk_ext <;> norm_num [term23Value,J_arg23]
  · rfl
  · intro n hn
    have hlt : n < 12 := by omega
    interval_cases n <;> norm_num [J_term23,J_arg23,sum, CertifiedTaylorModel.get, CertifiedTaylorModel.mul, CertifiedTaylorModel.add, exact, zero, qmul, qadd, size]

def J_log24 : Jet 12 := fun k =>
  match k.val with
  | 0 => ⟨((1589026915173973/500000000000000), 0), (1/125000000000000), by norm_num⟩
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

theorem S_log24 : Sound J_log24 F_log24 c := by
  have h := constant_sound (d:=12) (c:=c) RectangleLogInputs.log24_contains
  convert h using 1
  all_goals first | (funext k; fin_cases k <;> rfl) | rfl

def J_negLog24 : Jet 12 := fun k =>
  match k.val with
  | 0 => ⟨((-853102329/268435456), 0), (1/536870912), by norm_num⟩
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
theorem S_negLog24 : Sound J_negLog24 F_negLog24 c := by
  apply sound_round (sound_scale (A_log24 hcre) S_log24)
  intro k
  fin_cases k <;> norm_num [J_negLog24, J_log24, jetScale, sum, CertifiedTaylorModel.get, CertifiedTaylorModel.mul, CertifiedTaylorModel.add, exact, zero, qmul, qadd, size]

def J_arg24 : Jet 12 := fun k =>
  match k.val with
  | 0 => ⟨((-66648619/33554432), (-1468352397/33554432)), (1/16777216), by norm_num⟩
  | 1 => ⟨((-853102329/268435456), 0), (1/536870912), by norm_num⟩
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
theorem S_arg24 : Sound J_arg24 F_arg24 c := by
  apply sound_round (sound_mul (A_negLog24 hcre) (A_variable hcre) S_negLog24 S_variable)
  intro k
  fin_cases k <;> norm_num [J_arg24, J_negLog24, J_variable, jetMul, sum, CertifiedTaylorModel.get, CertifiedTaylorModel.mul, CertifiedTaylorModel.add, exact, zero, qmul, qadd, size]

def J_term24 : Jet 12 := fun k =>
  match k.val with
  | 0 => ⟨((1205502722176753/9007199254740992), (272088328932475/9007199254740992)), (93426517/9007199254740992), by norm_num⟩
  | 1 => ⟨((-456708973/1073741824), (-206163253/2147483648)), (73/2147483648), by norm_num⟩
  | 2 => ⟨((1451445701/2147483648), (163799479/1073741824)), (59/1073741824), by norm_num⟩
  | 3 => ⟨((-192198857/268435456), (-173521187/1073741824)), (127/2147483648), by norm_num⟩
  | 4 => ⟨((1221636627/2147483648), (68932459/536870912)), (103/2147483648), by norm_num⟩
  | 5 => ⟨((-48530337/134217728), (-350513705/4294967296)), (133/4294967296), by norm_num⟩
  | 6 => ⟨((1645141583/8589934592), (371317141/8589934592)), (143/8589934592), by norm_num⟩
  | 7 => ⟨((-373453465/4294967296), (-337161675/17179869184)), (33/4294967296), by norm_num⟩
  | 8 => ⟨((1186855215/34359738368), (4185617/536870912)), (107/34359738368), by norm_num⟩
  | 9 => ⟨((-838197725/68719476736), (-378371303/137438953472)), (77/68719476736), by norm_num⟩
  | 10 => ⟨((266383749/68719476736), (120248437/137438953472)), (99/274877906944), by norm_num⟩
  | 11 => ⟨((-1231391845/1099511627776), (-277931641/1099511627776)), (117/1099511627776), by norm_num⟩
  | 12 => ⟨((1304476523/4398046511104), (294427239/4398046511104)), (63/2199023255552), by norm_num⟩
  | _ => zero

def term24ValuePoly : ℕ → Disk
  | 20 => ⟨(0, 0), 0, by norm_num⟩
  | 19 => ⟨((666937165097003/81129638414606681695789005144064), 0), (1/162259276829213363391578010288128), by norm_num⟩
  | 18 => ⟨((1581388410907415/10141204801825835211973625643008), (289161075869/10141204801825835211973625643008)), (77643/10141204801825835211973625643008), by norm_num⟩
  | 17 => ⟨((1778905208596023/633825300114114700748351602688), (10695530897/19807040628566084398385987584)), (46117/316912650057057350374175801344), by norm_num⟩
  | 16 => ⟨((1889895363931113/39614081257132168796771975168), (384972250849/39614081257132168796771975168)), (51883/19807040628566084398385987584), by norm_num⟩
  | 15 => ⟨((118105003982827/154742504910672534362390528), (408950156717/2475880078570760549798248448)), (55127/1237940039285380274899124224), by norm_num⟩
  | 14 => ⟨((442836587254785/38685626227668133590597632), (102214243165/38685626227668133590597632)), (6891/9671406556917033397649408), by norm_num⟩
  | 13 => ⟨((774849698067637/4835703278458516698824704), (191602216875/4835703278458516698824704)), (103369/9671406556917033397649408), by norm_num⟩
  | 12 => ⟨((19670569468347/9444732965739290427392), (167602467553/302231454903657293676544)), (90451/604462909807314587353088), by norm_num⟩
  | 11 => ⟨((117999983114649/4722366482869645213696), (544522570319/75557863725914323419136)), (36747/18889465931478580854784), by norm_num⟩
  | 10 => ⟨((1297695278648741/4722366482869645213696), (408229731201/4722366482869645213696)), (55123/2361183241434822606848), by norm_num⟩
  | 9 => ⟨((1621662474064377/590295810358705651712), (561052445089/590295810358705651712)), (151595/590295810358705651712), by norm_num⟩
  | 8 => ⟨((1823742715993031/73786976294838206464), (87615079733/9223372036854775808)), (94753/36893488147419103232), by norm_num⟩
  | 7 => ⟨((28483729579565/144115188075855872), (393996542711/4611686018427387904)), (213211/9223372036854775808), by norm_num⟩
  | 6 => ⟨((1594207430139113/1152921504606846976), (196828841473/288230376151711744)), (213233/1152921504606846976), by norm_num⟩
  | 5 => ⟨((149346861872419/18014398509481984), (688139294649/144115188075855872)), (93301/72057594037927936), by norm_num⟩
  | 4 => ⟨((1491929115740829/36028797018963968), (515343799343/18014398509481984)), (279951/36028797018963968), by norm_num⟩
  | 3 => ⟨((744811611376027/4503599627370496), (1285701546467/9007199254740992)), (175011/4503599627370496), by norm_num⟩
  | 2 => ⟨((2228681847828267/4503599627370496), (2563446802685/4503599627370496)), (350149/2251799813685248), by norm_num⟩
  | 1 => ⟨((2217211037751777/2251799813685248), (3825340822451/2251799813685248)), (1051087/2251799813685248), by norm_num⟩
  | 0 => ⟨((2182973889317253/2251799813685248), (7571731105745/2251799813685248)), (2104769/2251799813685248), by norm_num⟩
  | _ => zero

def term24ValueSquares : ℕ → Disk
  | 0 => ⟨((2182973889317253/2251799813685248), (7571731105745/2251799813685248)), (8029056557662200217/8589934592000000000000000000), by norm_num⟩
  | 1 => ⟨((33066033732827/35184372088832), (14680604554915/2251799813685248)), (2047515/1125899906842624), by norm_num⟩
  | 2 => ⟨((1988719249486727/2251799813685248), (27593464746537/2251799813685248)), (3875179/1125899906842624), by norm_num⟩
  | 3 => ⟨((878018292290135/1125899906842624), (48739372095127/2251799813685248)), (6939847/1125899906842624), by norm_num⟩
  | 4 => ⟨((684183589781309/1125899906842624), (19004380404589/562949953421312)), (11124319/1125899906842624), by norm_num⟩
  | 5 => ⟨((207239789164055/562949953421312), (46194107052533/1125899906842624)), (57084281/4503599627370496), by norm_num⟩
  | 6 => ⟨((1205502722176753/9007199254740992), (272088328932475/9007199254740992)), (93426517/9007199254740992), by norm_num⟩
  | _ => zero

def term24Value : CertifiedScalarExp.Data :=
  ⟨⟨((-66648619/33554432), (-1468352397/33554432)), (1/16777216), by norm_num⟩, -7, term24ValuePoly, term24ValueSquares⟩

set_option maxHeartbeats 5000000 in
-- A bounded Horner table and six outward-rounded squarings.
theorem term24Value_checks : CertifiedScalarExp.Checks term24Value := by
  constructor
  · norm_num [term24Value, CertifiedScalarExp.reduced, term24ValuePoly, term24ValueSquares,
      CertifiedScalarExp.piDisk, CertifiedTaylorModel.mul, CertifiedTaylorModel.add,
      exact, qmul, qadd, size]
  · rfl
  · intro k hk
    interval_cases k <;>
      norm_num [term24Value, CertifiedScalarExp.roundingCheck, CertifiedScalarExp.reduced,
        term24ValuePoly, CertifiedScalarExp.piDisk, CertifiedTaylorModel.mul,
        CertifiedTaylorModel.add, exact, qmul, qadd, size]
  · apply CertifiedScalarExp.disk_ext <;> norm_num [term24Value, term24ValueSquares, term24ValuePoly, inflate]
  · intro k hk
    interval_cases k <;>
      norm_num [term24Value, CertifiedScalarExp.roundingCheck, term24ValueSquares,
        CertifiedTaylorModel.mul, exact, qmul, qadd, size]

set_option maxHeartbeats 5000000 in
theorem S_term24 : Sound J_term24 F_term24 c := by
  apply exp_sound (A_arg24 hcre) S_arg24 term24Value term24Value_checks
  · apply CertifiedScalarExp.disk_ext <;> norm_num [term24Value,J_arg24]
  · rfl
  · intro n hn
    have hlt : n < 12 := by omega
    interval_cases n <;> norm_num [J_term24,J_arg24,sum, CertifiedTaylorModel.get, CertifiedTaylorModel.mul, CertifiedTaylorModel.add, exact, zero, qmul, qadd, size]

def J_log25 : Jet 12 := fun k =>
  match k.val with
  | 0 => ⟨((16094379124341/5000000000000), 0), (1/125000000000000), by norm_num⟩
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

theorem S_log25 : Sound J_log25 F_log25 c := by
  have h := constant_sound (d:=12) (c:=c) RectangleLogInputs.log25_contains
  convert h using 1
  all_goals first | (funext k; fin_cases k <;> rfl) | rfl

def J_negLog25 : Jet 12 := fun k =>
  match k.val with
  | 0 => ⟨((-54003775/16777216), 0), (1/536870912), by norm_num⟩
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
theorem S_negLog25 : Sound J_negLog25 F_negLog25 c := by
  apply sound_round (sound_scale (A_log25 hcre) S_log25)
  intro k
  fin_cases k <;> norm_num [J_negLog25, J_log25, jetScale, sum, CertifiedTaylorModel.get, CertifiedTaylorModel.mul, CertifiedTaylorModel.add, exact, zero, qmul, qadd, size]

def J_arg25 : Jet 12 := fun k =>
  match k.val with
  | 0 => ⟨((-67504719/33554432), (-1487213335/33554432)), (1/16777216), by norm_num⟩
  | 1 => ⟨((-54003775/16777216), 0), (1/536870912), by norm_num⟩
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
theorem S_arg25 : Sound J_arg25 F_arg25 c := by
  apply sound_round (sound_mul (A_negLog25 hcre) (A_variable hcre) S_negLog25 S_variable)
  intro k
  fin_cases k <;> norm_num [J_arg25, J_negLog25, J_variable, jetMul, sum, CertifiedTaylorModel.get, CertifiedTaylorModel.mul, CertifiedTaylorModel.add, exact, zero, qmul, qadd, size]

def J_term25 : Jet 12 := fun k =>
  match k.val with
  | 0 => ⟨((567843189361383/4503599627370496), (-401879980173121/9007199254740992)), (50259695/4503599627370496), by norm_num⟩
  | 1 => ⟨((-54473183/134217728), (77104673/536870912)), (79/2147483648), by norm_num⟩
  | 2 => ⟨((1402739295/2147483648), (-7755949/33554432)), (129/2147483648), by norm_num⟩
  | 3 => ⟨((-752540601/1073741824), (33287249/134217728)), (35/536870912), by norm_num⟩
  | 4 => ⟨((605583687/1073741824), (-107147521/536870912)), (115/2147483648), by norm_num⟩
  | 5 => ⟨((-194929869/536870912), (68978913/536870912)), (75/2147483648), by norm_num⟩
  | 6 => ⟨((209151681/1073741824), (-148023037/2147483648)), (41/2147483648), by norm_num⟩
  | 7 => ⟨((-384704737/4294967296), (68066825/2147483648)), (153/17179869184), by norm_num⟩
  | 8 => ⟨((619158389/17179869184), (-438197315/34359738368)), (125/34359738368), by norm_num⟩
  | 9 => ⟨((-442887549/34359738368), (156722527/34359738368)), (91/68719476736), by norm_num⟩
  | 10 => ⟨((285120005/68719476736), (-403576283/274877906944)), (119/274877906944), by norm_num⟩
  | 11 => ⟨((-667466103/549755813888), (29524135/68719476736)), (141/1099511627776), by norm_num⟩
  | 12 => ⟨((716163501/2199023255552), (-506850797/4398046511104)), (153/4398046511104), by norm_num⟩
  | _ => zero

def term25ValuePoly : ℕ → Disk
  | 20 => ⟨(0, 0), 0, by norm_num⟩
  | 19 => ⟨((666937165097003/81129638414606681695789005144064), 0), (1/162259276829213363391578010288128), by norm_num⟩
  | 18 => ⟨((49417349261741/316912650057057350374175801344), (-13844894173/316912650057057350374175801344)), (77643/10141204801825835211973625643008), by norm_num⟩
  | 17 => ⟨((889432893941761/316912650057057350374175801344), (-131091289611/158456325028528675187087900672)), (23063/158456325028528675187087900672), by norm_num⟩
  | 16 => ⟨((944925509291481/19807040628566084398385987584), (-294903541629/19807040628566084398385987584)), (103787/39614081257132168796771975168), by norm_num⟩
  | 15 => ⟨((944816475084403/1237940039285380274899124224), (-156635361643/618970019642690137449562112)), (55139/1237940039285380274899124224), by norm_num⟩
  | 14 => ⟨((885649619631293/77371252455336267181195264), (-626396846725/154742504910672534362390528)), (55141/77371252455336267181195264), by norm_num⟩
  | 13 => ⟨((774827617388489/4835703278458516698824704), (-587093453277/9671406556917033397649408)), (51697/4835703278458516698824704), by norm_num⟩
  | 12 => ⟨((1258877808825425/604462909807314587353088), (-513553233761/604462909807314587353088)), (45237/302231454903657293676544), by norm_num⟩
  | 11 => ⟨((1887936952044755/75557863725914323419136), (-834236233263/75557863725914323419136)), (147029/75557863725914323419136), by norm_num⟩
  | 10 => ⟨((1297648201939171/4722366482869645213696), (-625425486629/4722366482869645213696)), (110279/4722366482869645213696), by norm_num⟩
  | 9 => ⟨((1621597754371743/590295810358705651712), (-859551260173/590295810358705651712)), (75823/295147905179352825856), by norm_num⟩
  | 8 => ⟨((1823661832560449/73786976294838206464), (-1073826265845/73786976294838206464)), (189577/73786976294838206464), by norm_num⟩
  | 7 => ⟨((455716930374121/2305843009213693952), (-1207212531419/9223372036854775808)), (213299/9223372036854775808), by norm_num⟩
  | 6 => ⟨((797058243198475/576460752303423488), (-301540225371/288230376151711744)), (213331/1152921504606846976), by norm_num⟩
  | 5 => ⟨((597347675284505/72057594037927936), (-1054208930665/144115188075855872)), (186701/144115188075855872), by norm_num⟩
  | 4 => ⟨((372952465481319/9007199254740992), (-1578952740159/36028797018963968)), (280123/36028797018963968), by norm_num⟩
  | 3 => ⟨((372368566385879/2251799813685248), (-984783327013/4503599627370496)), (350281/9007199254740992), by norm_num⟩
  | 2 => ⟨((2228384264234273/4503599627370496), (-3926787953671/4503599627370496)), (700945/4503599627370496), by norm_num⟩
  | 1 => ⟨((554191372910985/562949953421312), (-5859414440227/2251799813685248)), (1052381/2251799813685248), by norm_num⟩
  | 0 => ⟨((2182086127460675/2251799813685248), (-362385393951/70368744177664)), (2108655/2251799813685248), by norm_num⟩
  | _ => zero

def term25ValueSquares : ℕ → Disk
  | 0 => ⟨((2182086127460675/2251799813685248), (-362385393951/70368744177664)), (8043880471236418967/8589934592000000000000000000), by norm_num⟩
  | 1 => ⟨((2114470995063303/2251799813685248), (-11237320633979/1125899906842624)), (4108465/2251799813685248), by norm_num⟩
  | 2 => ⟨((1985293031953659/2251799813685248), (-42207994508869/2251799813685248)), (7797823/2251799813685248), by norm_num⟩
  | 3 => ⟨((1749536918859503/2251799813685248), (-74425121524509/2251799813685248)), (14042185/2251799813685248), by norm_num⟩
  | 4 => ⟨((1356843673744763/2251799813685248), (-57824632991969/1125899906842624)), (22748393/2251799813685248), by norm_num⟩
  | 5 => ⟨((1623279290770939/4503599627370496), (-278742317980253/4503599627370496)), (59502357/4503599627370496), by norm_num⟩
  | 6 => ⟨((567843189361383/4503599627370496), (-401879980173121/9007199254740992)), (50259695/4503599627370496), by norm_num⟩
  | _ => zero

def term25Value : CertifiedScalarExp.Data :=
  ⟨⟨((-67504719/33554432), (-1487213335/33554432)), (1/16777216), by norm_num⟩, -7, term25ValuePoly, term25ValueSquares⟩

set_option maxHeartbeats 5000000 in
-- A bounded Horner table and six outward-rounded squarings.
theorem term25Value_checks : CertifiedScalarExp.Checks term25Value := by
  constructor
  · norm_num [term25Value, CertifiedScalarExp.reduced, term25ValuePoly, term25ValueSquares,
      CertifiedScalarExp.piDisk, CertifiedTaylorModel.mul, CertifiedTaylorModel.add,
      exact, qmul, qadd, size]
  · rfl
  · intro k hk
    interval_cases k <;>
      norm_num [term25Value, CertifiedScalarExp.roundingCheck, CertifiedScalarExp.reduced,
        term25ValuePoly, CertifiedScalarExp.piDisk, CertifiedTaylorModel.mul,
        CertifiedTaylorModel.add, exact, qmul, qadd, size]
  · apply CertifiedScalarExp.disk_ext <;> norm_num [term25Value, term25ValueSquares, term25ValuePoly, inflate]
  · intro k hk
    interval_cases k <;>
      norm_num [term25Value, CertifiedScalarExp.roundingCheck, term25ValueSquares,
        CertifiedTaylorModel.mul, exact, qmul, qadd, size]

set_option maxHeartbeats 5000000 in
theorem S_term25 : Sound J_term25 F_term25 c := by
  apply exp_sound (A_arg25 hcre) S_arg25 term25Value term25Value_checks
  · apply CertifiedScalarExp.disk_ext <;> norm_num [term25Value,J_arg25]
  · rfl
  · intro n hn
    have hlt : n < 12 := by omega
    interval_cases n <;> norm_num [J_term25,J_arg25,sum, CertifiedTaylorModel.get, CertifiedTaylorModel.mul, CertifiedTaylorModel.add, exact, zero, qmul, qadd, size]

def J_log26 : Jet 12 := fun k =>
  match k.val with
  | 0 => ⟨((1629048269010741/500000000000000), 0), (1/125000000000000), by norm_num⟩
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

theorem S_log26 : Sound J_log26 F_log26 c := by
  have h := constant_sound (d:=12) (c:=c) RectangleLogInputs.log26_contains
  convert h using 1
  all_goals first | (funext k; fin_cases k <;> rfl) | rfl

def J_negLog26 : Jet 12 := fun k =>
  match k.val with
  | 0 => ⟨((-437294315/134217728), 0), (1/536870912), by norm_num⟩
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
theorem S_negLog26 : Sound J_negLog26 F_negLog26 c := by
  apply sound_round (sound_scale (A_log26 hcre) S_log26)
  intro k
  fin_cases k <;> norm_num [J_negLog26, J_log26, jetScale, sum, CertifiedTaylorModel.get, CertifiedTaylorModel.mul, CertifiedTaylorModel.add, exact, zero, qmul, qadd, size]

def J_arg26 : Jet 12 := fun k =>
  match k.val with
  | 0 => ⟨((-68327237/33554432), (-752667217/16777216)), (1/16777216), by norm_num⟩
  | 1 => ⟨((-437294315/134217728), 0), (1/536870912), by norm_num⟩
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
theorem S_arg26 : Sound J_arg26 F_arg26 c := by
  apply sound_round (sound_mul (A_negLog26 hcre) (A_variable hcre) S_negLog26 S_variable)
  intro k
  fin_cases k <;> norm_num [J_arg26, J_negLog26, J_variable, jetMul, sum, CertifiedTaylorModel.get, CertifiedTaylorModel.mul, CertifiedTaylorModel.add, exact, zero, qmul, qadd, size]

def J_term26 : Jet 12 := fun k =>
  match k.val with
  | 0 => ⟨((748836868642491/9007199254740992), (-453072712948159/4503599627370496)), (35273549/2251799813685248), by norm_num⟩
  | 1 => ⟨((-581689551/2147483648), (703885383/2147483648)), (7/134217728), by norm_num⟩
  | 2 => ⟨((236900089/536870912), (-1146663265/2147483648)), (185/2147483648), by norm_num⟩
  | 3 => ⟨((-8040035/16777216), (311328301/536870912)), (51/536870912), by norm_num⟩
  | 4 => ⟨((419123363/1073741824), (-253584415/536870912)), (21/268435456), by norm_num⟩
  | 5 => ⟨((-546217751/2147483648), (165240501/536870912)), (111/2147483648), by norm_num⟩
  | 6 => ⟨((593210055/4294967296), (-358913003/2147483648)), (61/2147483648), by norm_num⟩
  | 7 => ⟨((-552210179/8589934592), (41763329/536870912)), (115/8589934592), by norm_num⟩
  | 8 => ⟨((224894259/8589934592), (-1088551661/34359738368)), (95/17179869184), by norm_num⟩
  | 9 => ⟨((-651313073/68719476736), (788134755/68719476736)), (139/68719476736), by norm_num⟩
  | 10 => ⟨((848816347/274877906944), (-1027127647/274877906944)), (183/274877906944), by norm_num⟩
  | 11 => ⟨((-502822837/549755813888), (608451097/549755813888)), (55/274877906944), by norm_num⟩
  | 12 => ⟨((273040891/1099511627776), (-660797471/2199023255552)), (121/2199023255552), by norm_num⟩
  | _ => zero

def term26ValuePoly : ℕ → Disk
  | 20 => ⟨(0, 0), 0, by norm_num⟩
  | 19 => ⟨((666937165097003/81129638414606681695789005144064), 0), (1/162259276829213363391578010288128), by norm_num⟩
  | 18 => ⟨((1581323245525873/10141204801825835211973625643008), (-1146513122353/10141204801825835211973625643008)), (77643/10141204801825835211973625643008), by norm_num⟩
  | 17 => ⟨((889413578955655/316912650057057350374175801344), (-339231114189/158456325028528675187087900672)), (46167/316912650057057350374175801344), by norm_num⟩
  | 16 => ⟨((944903759998111/19807040628566084398385987584), (-763133888049/19807040628566084398385987584)), (25971/9903520314283042199192993792), by norm_num⟩
  | 15 => ⟨((944793340315761/1237940039285380274899124224), (-1621322648791/2475880078570760549798248448)), (110387/2475880078570760549798248448), by norm_num⟩
  | 14 => ⟨((885626455476871/77371252455336267181195264), (-810471902379/77371252455336267181195264)), (110399/154742504910672534362390528), by norm_num⟩
  | 13 => ⟨((387402934896301/2417851639229258349412352), (-759616206385/4835703278458516698824704)), (51755/4835703278458516698824704), by norm_num⟩
  | 12 => ⟨((1258839688178285/604462909807314587353088), (-1328926089289/604462909807314587353088)), (90583/604462909807314587353088), by norm_num⟩
  | 11 => ⟨((1887874889180485/75557863725914323419136), (-2158750916357/75557863725914323419136)), (36805/18889465931478580854784), by norm_num⟩
  | 10 => ⟨((1297601552681529/4722366482869645213696), (-809201868403/2361183241434822606848)), (110435/4722366482869645213696), by norm_num⟩
  | 9 => ⟨((1621533445905079/590295810358705651712), (-139014628601/36893488147419103232)), (151879/590295810358705651712), by norm_num⟩
  | 8 => ⟨((56986912459499/2305843009213693952), (-2778686872187/73786976294838206464)), (23737/9223372036854775808), by norm_num⟩
  | 7 => ⟨((1822776667572853/9223372036854775808), (-24404815543/72057594037927936)), (213699/9223372036854775808), by norm_num⟩
  | 6 => ⟨((1594025007239217/1152921504606846976), (-3121060704129/1152921504606846976)), (213781/1152921504606846976), by norm_num⟩
  | 5 => ⟨((1194614829029449/144115188075855872), (-2727831049909/144115188075855872)), (187151/144115188075855872), by norm_num⟩
  | 4 => ⟨((1491688127837615/36028797018963968), (-4085560134339/36028797018963968)), (280911/36028797018963968), by norm_num⟩
  | 3 => ⟨((1489320438551979/9007199254740992), (-1274035295631/2251799813685248)), (351463/9007199254740992), by norm_num⟩
  | 2 => ⟨((2228071656960165/4503599627370496), (-10159924444955/4503599627370496)), (703901/4503599627370496), by norm_num⟩
  | 1 => ⟨((1108142142101429/1125899906842624), (-15159233017363/2251799813685248)), (1058297/2251799813685248), by norm_num⟩
  | 0 => ⟨((2181075044296875/2251799813685248), (-7499323633081/562949953421312)), (2126421/2251799813685248), by norm_num⟩
  | _ => zero

def term26ValueSquares : ℕ → Disk
  | 0 => ⟨((2181075044296875/2251799813685248), (-7499323633081/562949953421312)), (8111652382857512717/8589934592000000000000000000), by norm_num⟩
  | 1 => ⟨((1056085998912905/1125899906842624), (-29055136297307/1125899906842624)), (1043981/562949953421312), by norm_num⟩
  | 2 => ⟨((989851255321573/1125899906842624), (-109014033853655/2251799813685248)), (251547/70368744177664), by norm_num⟩
  | 3 => ⟨((1735206632189503/2251799813685248), (-191682542296883/2251799813685248)), (7466531/1125899906842624), by norm_num⟩
  | 4 => ⟨((1320810065485141/2251799813685248), (-295415974943311/2251799813685248)), (25556763/2251799813685248), by norm_num⟩
  | 5 => ⟨((1471950233553759/4503599627370496), (-693113820933589/4503599627370496)), (9171665/562949953421312), by norm_num⟩
  | 6 => ⟨((748836868642491/9007199254740992), (-453072712948159/4503599627370496)), (35273549/2251799813685248), by norm_num⟩
  | _ => zero

def term26Value : CertifiedScalarExp.Data :=
  ⟨⟨((-68327237/33554432), (-752667217/16777216)), (1/16777216), by norm_num⟩, -7, term26ValuePoly, term26ValueSquares⟩

set_option maxHeartbeats 5000000 in
-- A bounded Horner table and six outward-rounded squarings.
theorem term26Value_checks : CertifiedScalarExp.Checks term26Value := by
  constructor
  · norm_num [term26Value, CertifiedScalarExp.reduced, term26ValuePoly, term26ValueSquares,
      CertifiedScalarExp.piDisk, CertifiedTaylorModel.mul, CertifiedTaylorModel.add,
      exact, qmul, qadd, size]
  · rfl
  · intro k hk
    interval_cases k <;>
      norm_num [term26Value, CertifiedScalarExp.roundingCheck, CertifiedScalarExp.reduced,
        term26ValuePoly, CertifiedScalarExp.piDisk, CertifiedTaylorModel.mul,
        CertifiedTaylorModel.add, exact, qmul, qadd, size]
  · apply CertifiedScalarExp.disk_ext <;> norm_num [term26Value, term26ValueSquares, term26ValuePoly, inflate]
  · intro k hk
    interval_cases k <;>
      norm_num [term26Value, CertifiedScalarExp.roundingCheck, term26ValueSquares,
        CertifiedTaylorModel.mul, exact, qmul, qadd, size]

set_option maxHeartbeats 5000000 in
theorem S_term26 : Sound J_term26 F_term26 c := by
  apply exp_sound (A_arg26 hcre) S_arg26 term26Value term26Value_checks
  · apply CertifiedScalarExp.disk_ext <;> norm_num [term26Value,J_arg26]
  · rfl
  · intro n hn
    have hlt : n < 12 := by omega
    interval_cases n <;> norm_num [J_term26,J_arg26,sum, CertifiedTaylorModel.get, CertifiedTaylorModel.mul, CertifiedTaylorModel.add, exact, zero, qmul, qadd, size]

def J_log27 : Jet 12 := fun k =>
  match k.val with
  | 0 => ⟨((3295836866004329/1000000000000000), 0), (1/125000000000000), by norm_num⟩
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

theorem S_log27 : Sound J_log27 F_log27 c := by
  have h := constant_sound (d:=12) (c:=c) RectangleLogInputs.log27_contains
  convert h using 1
  all_goals first | (funext k; fin_cases k <;> rfl) | rfl

def J_negLog27 : Jet 12 := fun k =>
  match k.val with
  | 0 => ⟨((-55294967/16777216), 0), (1/536870912), by norm_num⟩
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
theorem S_negLog27 : Sound J_negLog27 F_negLog27 c := by
  apply sound_round (sound_scale (A_log27 hcre) S_log27)
  intro k
  fin_cases k <;> norm_num [J_negLog27, J_log27, jetScale, sum, CertifiedTaylorModel.get, CertifiedTaylorModel.mul, CertifiedTaylorModel.add, exact, zero, qmul, qadd, size]

def J_arg27 : Jet 12 := fun k =>
  match k.val with
  | 0 => ⟨((-69118709/33554432), (-47586611/1048576)), (1/16777216), by norm_num⟩
  | 1 => ⟨((-55294967/16777216), 0), (1/536870912), by norm_num⟩
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
theorem S_arg27 : Sound J_arg27 F_arg27 c := by
  apply sound_round (sound_mul (A_negLog27 hcre) (A_variable hcre) S_negLog27 S_variable)
  intro k
  fin_cases k <;> norm_num [J_arg27, J_negLog27, J_variable, jetMul, sum, CertifiedTaylorModel.get, CertifiedTaylorModel.mul, CertifiedTaylorModel.add, exact, zero, qmul, qadd, size]

def J_term27 : Jet 12 := fun k =>
  match k.val with
  | 0 => ⟨((12208331390657/562949953421312), (-1131382003164865/9007199254740992)), (87291127/4503599627370496), by norm_num⟩
  | 1 => ⟨((-76745355/1073741824), (1778054483/4294967296)), (69/1073741824), by norm_num⟩
  | 2 => ⟨((126470085/1073741824), (-1465044379/2147483648)), (115/1073741824), by norm_num⟩
  | 3 => ⟨((-277883179/2147483648), (804757879/1073741824)), (127/1073741824), by norm_num⟩
  | 4 => ⟨((114482203/1073741824), (-1326175343/2147483648)), (211/2147483648), by norm_num⟩
  | 5 => ⟨((-75462933/1073741824), (874171517/2147483648)), (35/536870912), by norm_num⟩
  | 6 => ⟨((165809011/4294967296), (-960375571/4294967296)), (155/4294967296), by norm_num⟩
  | 7 => ⟨((-78068493/4294967296), (113044329/1073741824)), (147/8589934592), by norm_num⟩
  | 8 => ⟨((257301017/34359738368), (-372575667/8589934592)), (61/8589934592), by norm_num⟩
  | 9 => ⟨((-188449373/68719476736), (1091509883/68719476736)), (45/17179869184), by norm_num⟩
  | 10 => ⟨((62109839/68719476736), (-1438975405/274877906944)), (239/274877906944), by norm_num⟩
  | 11 => ⟨((-297751123/1099511627776), (1724592069/1099511627776)), (9/34359738368), by norm_num⟩
  | 12 => ⟨((163556521/2199023255552), (-236832255/549755813888)), (5/68719476736), by norm_num⟩
  | _ => zero

def term27ValuePoly : ℕ → Disk
  | 20 => ⟨(0, 0), 0, by norm_num⟩
  | 19 => ⟨((666937165097003/81129638414606681695789005144064), 0), (1/162259276829213363391578010288128), by norm_num⟩
  | 18 => ⟨((1581292519908217/10141204801825835211973625643008), (-1823436905755/10141204801825835211973625643008)), (38821/5070602400912917605986812821504), by norm_num⟩
  | 17 => ⟨((1778789286938257/633825300114114700748351602688), (-269749400531/79228162514264337593543950336)), (23103/158456325028528675187087900672), by norm_num⟩
  | 16 => ⟨((1889764837427811/39614081257132168796771975168), (-606826206467/9903520314283042199192993792)), (51989/19807040628566084398385987584), by norm_num⟩
  | 15 => ⟨((1889541228728583/2475880078570760549798248448), (-2578469208859/2475880078570760549798248448)), (27623/618970019642690137449562112), by norm_num⟩
  | 14 => ⟨((885603672383279/77371252455336267181195264), (-322232430681/19342813113834066795298816)), (55255/77371252455336267181195264), by norm_num⟩
  | 13 => ⟨((1549568899938481/9671406556917033397649408), (-4718936581/18889465931478580854784)), (51811/4835703278458516698824704), by norm_num⟩
  | 12 => ⟨((1258802082232067/604462909807314587353088), (-528359020559/151115727451828646838272)), (1417/9444732965739290427392), by norm_num⟩
  | 11 => ⟨((943906776178591/37778931862957161709568), (-3433119973163/75557863725914323419136)), (36851/18889465931478580854784), by norm_num⟩
  | 10 => ⟨((1297555351491371/4722366482869645213696), (-2573778440213/4722366482869645213696)), (13823/590295810358705651712), by norm_num⟩
  | 9 => ⟨((810734798474743/295147905179352825856), (-3537221127931/590295810358705651712)), (152103/590295810358705651712), by norm_num⟩
  | 8 => ⟨((1823500904662847/73786976294838206464), (-4418941423861/73786976294838206464)), (190205/73786976294838206464), by norm_num⟩
  | 7 => ⟨((455671418472145/2305843009213693952), (-2483878473445/4611686018427387904)), (53521/2305843009213693952), by norm_num⟩
  | 6 => ⟨((199241648310293/144115188075855872), (-4963320052757/1152921504606846976)), (214215/1152921504606846976), by norm_num⟩
  | 5 => ⟨((1194533557521635/144115188075855872), (-2168959037167/72057594037927936)), (187585/144115188075855872), by norm_num⟩
  | 4 => ⟨((745782184577073/18014398509481984), (-1624228623635/9007199254740992)), (140835/18014398509481984), by norm_num⟩
  | 3 => ⟨((1489162512042405/9007199254740992), (-2025933500065/2251799813685248)), (352603/9007199254740992), by norm_num⟩
  | 2 => ⟨((2227746166690615/4503599627370496), (-1009708898585/281474976710656)), (706751/4503599627370496), by norm_num⟩
  | 1 => ⟨((2215772120405271/2251799813685248), (-24103055041233/2251799813685248)), (532001/1125899906842624), by norm_num⟩
  | 0 => ⟨((2179955987367779/2251799813685248), (-47688404992443/2251799813685248)), (1071783/1125899906842624), by norm_num⟩
  | _ => zero

def term27ValueSquares : ℕ → Disk
  | 0 => ⟨((2179955987367779/2251799813685248), (-47688404992443/2251799813685248)), (4088527683738326671/4294967296000000000000000000), by norm_num⟩
  | 1 => ⟨((1054697201328093/1125899906842624), (-23083451592697/562949953421312)), (530143/281474976710656), by norm_num⟩
  | 2 => ⟨((1972208713744519/2251799813685248), (-86494551225549/1125899906842624)), (8293675/2251799813685248), by norm_num⟩
  | 3 => ⟨((1714043121216135/2251799813685248), (-75755094472307/562949953421312)), (3950523/562949953421312), by norm_num⟩
  | 4 => ⟨((631966139857325/1125899906842624), (-461310984353731/2251799813685248)), (28309643/2251799813685248), by norm_num⟩
  | 5 => ⟨((614937871032623/2251799813685248), (-517866500004179/2251799813685248)), (21689771/1125899906842624), by norm_num⟩
  | 6 => ⟨((12208331390657/562949953421312), (-1131382003164865/9007199254740992)), (87291127/4503599627370496), by norm_num⟩
  | _ => zero

def term27Value : CertifiedScalarExp.Data :=
  ⟨⟨((-69118709/33554432), (-47586611/1048576)), (1/16777216), by norm_num⟩, -7, term27ValuePoly, term27ValueSquares⟩

set_option maxHeartbeats 5000000 in
-- A bounded Horner table and six outward-rounded squarings.
theorem term27Value_checks : CertifiedScalarExp.Checks term27Value := by
  constructor
  · norm_num [term27Value, CertifiedScalarExp.reduced, term27ValuePoly, term27ValueSquares,
      CertifiedScalarExp.piDisk, CertifiedTaylorModel.mul, CertifiedTaylorModel.add,
      exact, qmul, qadd, size]
  · rfl
  · intro k hk
    interval_cases k <;>
      norm_num [term27Value, CertifiedScalarExp.roundingCheck, CertifiedScalarExp.reduced,
        term27ValuePoly, CertifiedScalarExp.piDisk, CertifiedTaylorModel.mul,
        CertifiedTaylorModel.add, exact, qmul, qadd, size]
  · apply CertifiedScalarExp.disk_ext <;> norm_num [term27Value, term27ValueSquares, term27ValuePoly, inflate]
  · intro k hk
    interval_cases k <;>
      norm_num [term27Value, CertifiedScalarExp.roundingCheck, term27ValueSquares,
        CertifiedTaylorModel.mul, exact, qmul, qadd, size]

set_option maxHeartbeats 5000000 in
theorem S_term27 : Sound J_term27 F_term27 c := by
  apply exp_sound (A_arg27 hcre) S_arg27 term27Value term27Value_checks
  · apply CertifiedScalarExp.disk_ext <;> norm_num [term27Value,J_arg27]
  · rfl
  · intro n hn
    have hlt : n < 12 := by omega
    interval_cases n <;> norm_num [J_term27,J_arg27,sum, CertifiedTaylorModel.get, CertifiedTaylorModel.mul, CertifiedTaylorModel.add, exact, zero, qmul, qadd, size]

def term22Jet : Jet 12 := J_term22
theorem term22Jet_sound : Sound term22Jet F_term22 (Data.centre ⟨37,by norm_num [Data.count]⟩) := S_term22

def term23Jet : Jet 12 := J_term23
theorem term23Jet_sound : Sound term23Jet F_term23 (Data.centre ⟨37,by norm_num [Data.count]⟩) := S_term23

def term24Jet : Jet 12 := J_term24
theorem term24Jet_sound : Sound term24Jet F_term24 (Data.centre ⟨37,by norm_num [Data.count]⟩) := S_term24

def term25Jet : Jet 12 := J_term25
theorem term25Jet_sound : Sound term25Jet F_term25 (Data.centre ⟨37,by norm_num [Data.count]⟩) := S_term25

def term26Jet : Jet 12 := J_term26
theorem term26Jet_sound : Sound term26Jet F_term26 (Data.centre ⟨37,by norm_num [Data.count]⟩) := S_term26

def term27Jet : Jet 12 := J_term27
theorem term27Jet_sound : Sound term27Jet F_term27 (Data.centre ⟨37,by norm_num [Data.count]⟩) := S_term27

end Reinmann.XiRectangle.Tile037Terms3
