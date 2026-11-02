/-
Copyright (c) 2026 Biswajit Mondal. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Biswajit Mondal
-/
-- Internal rounding: 36 bits, checked against fixed final error disks.
module

public import Reinmann.RectangleModel
public import XiRectangle.Data

@[expose] public section

/-! Numerical proposals for one closed ball. Every rounding check is proved
by rational arithmetic in the Lean kernel; no native evaluation is used. -/
noncomputable section
namespace Reinmann.XiRectangle.Tile011Terms2
open CertifiedTaylorModel CertifiedTaylorComposition RectangleTaylor RectangleModel
open scoped Topology
set_option maxRecDepth 30000
set_option linter.style.longLine false
set_option linter.style.whitespace false

def c : ℂ := Data.centre ⟨11,by norm_num [Data.count]⟩
theorem hc : c ∈ XiAdaptiveTiles.quarter (141/10) := Data.centre_mem_quarter _
theorem hcre : -2<c.re := by linarith [hc.1]

def J_variable : Jet 12 := fun k =>
  match k.val with
  | 0 => ⟨((3/4), (3243/640)), 0, by norm_num⟩
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
  have h := variable_sound 12 ((3/4), (3243/640))
  have he : value ((3/4), (3243/640))=c := by norm_num [c,Data.centre,Data.coordinate,value]
  rw [he] at h
  convert h using 1
  all_goals first | (funext k; fin_cases k <;> rfl) | rfl

def J_log16 : Jet 12 := fun k =>
  match k.val with
  | 0 => ⟨((2772588722239781/1000000000000000), 0), (3/500000000000000), by norm_num⟩
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

theorem S_log16 : Sound J_log16 F_log16 c := by
  have h := constant_sound (d:=12) (c:=c) RectangleLogInputs.log16_contains
  convert h using 1
  all_goals first | (funext k; fin_cases k <;> rfl) | rfl

def J_negLog16 : Jet 12 := fun k =>
  match k.val with
  | 0 => ⟨((-47632711549/17179869184), 0), (1/34359738368), by norm_num⟩
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
theorem S_negLog16 : Sound J_negLog16 F_negLog16 c := by
  apply sound_round (sound_scale (A_log16 hcre) S_log16)
  intro k
  fin_cases k <;> norm_num [J_negLog16, J_log16, jetScale, sum, CertifiedTaylorModel.get, CertifiedTaylorModel.mul, CertifiedTaylorModel.add, exact, zero, qmul, qadd, size]

def J_arg16 : Jet 12 := fun k =>
  match k.val with
  | 0 => ⟨((-8931133415/4294967296), (-30170485069/2147483648)), (1/2147483648), by norm_num⟩
  | 1 => ⟨((-47632711549/17179869184), 0), (1/34359738368), by norm_num⟩
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
theorem S_arg16 : Sound J_arg16 F_arg16 c := by
  apply sound_round (sound_mul (A_negLog16 hcre) (A_variable hcre) S_negLog16 S_variable)
  intro k
  fin_cases k <;> norm_num [J_arg16, J_negLog16, J_variable, jetMul, sum, CertifiedTaylorModel.get, CertifiedTaylorModel.mul, CertifiedTaylorModel.add, exact, zero, qmul, qadd, size]

def J_term16 : Jet 12 := fun k =>
  match k.val with
  | 0 => ⟨((98884098626275/9007199254740992), (-140193645960791/1125899906842624)), (1376755/9007199254740992), by norm_num⟩
  | 1 => ⟨((-4183424937/137438953472), (47448647671/137438953472)), (119/274877906944), by norm_num⟩
  | 2 => ⟨((181233075/4294967296), (-65777792709/137438953472)), (21/34359738368), by norm_num⟩
  | 3 => ⟨((-10719675303/274877906944), (30395794373/68719476736)), (79/137438953472), by norm_num⟩
  | 4 => ⟨((7430312713/274877906944), (-42137518341/137438953472)), (111/274877906944), by norm_num⟩
  | 5 => ⟨((-2060120123/137438953472), (23366001627/137438953472)), (125/549755813888), by norm_num⟩
  | 6 => ⟨((7615821093/1099511627776), (-21594770865/274877906944)), (59/549755813888), by norm_num⟩
  | 7 => ⟨((-6033011335/2199023255552), (68426763611/2199023255552)), (95/2199023255552), by norm_num⟩
  | 8 => ⟨((4181764797/4398046511104), (-94859636543/8796093022208)), (67/4398046511104), by norm_num⟩
  | 9 => ⟨((-5153028407/17592186044416), (116891892655/35184372088832)), (21/4398046511104), by norm_num⟩
  | 10 => ⟨((5714891379/70368744177664), (-64818628659/70368744177664)), (95/70368744177664), by norm_num⟩
  | 11 => ⟨((-5761833959/281474976710656), (65351054113/281474976710656)), (97/281474976710656), by norm_num⟩
  | 12 => ⟨((10650130569/2251799813685248), (-15099299635/281474976710656)), (91/1125899906842624), by norm_num⟩
  | _ => zero

def term16ValuePoly : ℕ → Disk
  | 20 => ⟨(0, 0), 0, by norm_num⟩
  | 19 => ⟨((666937165097003/81129638414606681695789005144064), 0), (1/162259276829213363391578010288128), by norm_num⟩
  | 18 => ⟨((1581267062326629/10141204801825835211973625643008), (-965792947281/5070602400912917605986812821504)), (19/316912650057057350374175801344), by norm_num⟩
  | 17 => ⟨((1778758854515001/633825300114114700748351602688), (-2285913288951/633825300114114700748351602688)), (723/633825300114114700748351602688), by norm_num⟩
  | 16 => ⟨((1889730590040569/39614081257132168796771975168), (-1285590992841/19807040628566084398385987584)), (813/39614081257132168796771975168), by norm_num⟩
  | 15 => ⟨((472376206531315/618970019642690137449562112), (-682825266377/618970019642690137449562112)), (865/2475880078570760549798248448), by norm_num⟩
  | 14 => ⟨((885585462791983/77371252455336267181195264), (-1365324490903/77371252455336267181195264)), (865/154742504910672534362390528), by norm_num⟩
  | 13 => ⟨((1549534739354797/9671406556917033397649408), (-2559290764875/9671406556917033397649408)), (811/9671406556917033397649408), by norm_num⟩
  | 12 => ⟨((629386087069373/302231454903657293676544), (-1119343484971/302231454903657293676544)), (355/302231454903657293676544), by norm_num⟩
  | 11 => ⟨((1887764918775133/75557863725914323419136), (-1818284210917/37778931862957161709568)), (1153/75557863725914323419136), by norm_num⟩
  | 10 => ⟨((1297518847527675/4722366482869645213696), (-2726291088129/4722366482869645213696)), (865/4722366482869645213696), by norm_num⟩
  | 9 => ⟨((405354839326433/147573952589676412928), (-3746806321327/590295810358705651712)), (595/295147905179352825856), by norm_num⟩
  | 8 => ⟨((455859508797165/18446744073709551616), (-4680743450695/73786976294838206464)), (93/4611686018427387904), by norm_num⟩
  | 7 => ⟨((1822614849787251/9223372036854775808), (-1315509398743/2305843009213693952)), (837/4611686018427387904), by norm_num⟩
  | 6 => ⟨((398465560686683/288230376151711744), (-2628646304467/576460752303423488)), (1675/1152921504606846976), by norm_num⟩
  | 5 => ⟨((597235673784243/72057594037927936), (-4594797730165/144115188075855872)), (1467/144115188075855872), by norm_num⟩
  | 4 => ⟨((745735393431955/18014398509481984), (-6881541998093/36028797018963968)), (2203/36028797018963968), by norm_num⟩
  | 3 => ⟨((1489045068562963/9007199254740992), (-1072913618461/1125899906842624)), (2757/9007199254740992), by norm_num⟩
  | 2 => ⟨((2227509891914891/4503599627370496), (-4277717527443/1125899906842624)), (2763/2251799813685248), by norm_num⟩
  | 1 => ⟨((1107707135104029/1125899906842624), (-1595457043905/140737488355328)), (65/17592186044416), by norm_num⟩
  | 0 => ⟨((2179226723032633/2251799813685248), (-25250456692879/1125899906842624)), (16769/2251799813685248), by norm_num⟩
  | _ => zero

def term16ValueSquares : ℕ → Disk
  | 0 => ⟨((2179226723032633/2251799813685248), (-25250456692879/1125899906842624)), (63968667037200217/8589934592000000000000000000), by norm_num⟩
  | 1 => ⟨((526965001426877/562949953421312), (-97746646321717/2251799813685248)), (16605/1125899906842624), by norm_num⟩
  | 2 => ⟨((246109765722153/281474976710656), (-182996947793853/2251799813685248)), (65059/2251799813685248), by norm_num⟩
  | 3 => ⟨((1706631809766787/2251799813685248), (-320009518968435/2251799813685248)), (124345/2251799813685248), by norm_num⟩
  | 4 => ⟨((155996662358629/281474976710656), (-485068362809659/2251799813685248)), (13989/140737488355328), by norm_num⟩
  | 5 => ⟨((587150789362317/2251799813685248), (-1075321813659561/4503599627370496)), (689043/4503599627370496), by norm_num⟩
  | 6 => ⟨((98884098626275/9007199254740992), (-140193645960791/1125899906842624)), (1376755/9007199254740992), by norm_num⟩
  | _ => zero

def term16Value : CertifiedScalarExp.Data :=
  ⟨⟨((-8931133415/4294967296), (-30170485069/2147483648)), (1/2147483648), by norm_num⟩, -2, term16ValuePoly, term16ValueSquares⟩

set_option maxHeartbeats 5000000 in
-- A bounded Horner table and six outward-rounded squarings.
theorem term16Value_checks : CertifiedScalarExp.Checks term16Value := by
  constructor
  · norm_num [term16Value, CertifiedScalarExp.reduced, term16ValuePoly, term16ValueSquares,
      CertifiedScalarExp.piDisk, CertifiedTaylorModel.mul, CertifiedTaylorModel.add,
      exact, qmul, qadd, size]
  · rfl
  · intro k hk
    interval_cases k <;>
      norm_num [term16Value, CertifiedScalarExp.roundingCheck, CertifiedScalarExp.reduced,
        term16ValuePoly, CertifiedScalarExp.piDisk, CertifiedTaylorModel.mul,
        CertifiedTaylorModel.add, exact, qmul, qadd, size]
  · apply CertifiedScalarExp.disk_ext <;> norm_num [term16Value, term16ValueSquares, term16ValuePoly, inflate]
  · intro k hk
    interval_cases k <;>
      norm_num [term16Value, CertifiedScalarExp.roundingCheck, term16ValueSquares,
        CertifiedTaylorModel.mul, exact, qmul, qadd, size]

set_option maxHeartbeats 5000000 in
theorem S_term16 : Sound J_term16 F_term16 c := by
  apply exp_sound (A_arg16 hcre) S_arg16 term16Value term16Value_checks
  · apply CertifiedScalarExp.disk_ext <;> norm_num [term16Value,J_arg16]
  · rfl
  · intro n hn
    have hlt : n < 12 := by omega
    interval_cases n <;> norm_num [J_term16,J_arg16,sum, CertifiedTaylorModel.get, CertifiedTaylorModel.mul, CertifiedTaylorModel.add, exact, zero, qmul, qadd, size]

def J_log17 : Jet 12 := fun k =>
  match k.val with
  | 0 => ⟨((354151668007027/125000000000000), 0), (3/500000000000000), by norm_num⟩
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

theorem S_log17 : Sound J_log17 F_log17 c := by
  have h := constant_sound (d:=12) (c:=c) RectangleLogInputs.log17_contains
  convert h using 1
  all_goals first | (funext k; fin_cases k <;> rfl) | rfl

def J_negLog17 : Jet 12 := fun k =>
  match k.val with
  | 0 => ⟨((-48674234621/17179869184), 0), (1/34359738368), by norm_num⟩
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
theorem S_negLog17 : Sound J_negLog17 F_negLog17 c := by
  apply sound_round (sound_scale (A_log17 hcre) S_log17)
  intro k
  fin_cases k <;> norm_num [J_negLog17, J_log17, jetScale, sum, CertifiedTaylorModel.get, CertifiedTaylorModel.mul, CertifiedTaylorModel.add, exact, zero, qmul, qadd, size]

def J_arg17 : Jet 12 := fun k =>
  match k.val with
  | 0 => ⟨((-9126418991/4294967296), (-61660368311/4294967296)), (1/2147483648), by norm_num⟩
  | 1 => ⟨((-48674234621/17179869184), 0), (1/34359738368), by norm_num⟩
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
theorem S_arg17 : Sound J_arg17 F_arg17 c := by
  apply sound_round (sound_mul (A_negLog17 hcre) (A_variable hcre) S_negLog17 S_variable)
  intro k
  fin_cases k <;> norm_num [J_arg17, J_negLog17, J_variable, jetMul, sum, CertifiedTaylorModel.get, CertifiedTaylorModel.mul, CertifiedTaylorModel.add, exact, zero, qmul, qadd, size]

def J_term17 : Jet 12 := fun k =>
  match k.val with
  | 0 => ⟨((-58500545231635/2251799813685248), (-525048432146455/4503599627370496)), (1431935/9007199254740992), by norm_num⟩
  | 1 => ⟨((20232486009/274877906944), (90794325209/274877906944)), (63/137438953472), by norm_num⟩
  | 2 => ⟨((-1791342167/17179869184), (-16077480859/34359738368)), (91/137438953472), by norm_num⟩
  | 3 => ⟨((13534012083/137438953472), (3795911109/8589934592)), (11/17179869184), by norm_num⟩
  | 4 => ⟨((-2396546477/34359738368), (-86037008055/274877906944)), (127/274877906944), by norm_num⟩
  | 5 => ⟨((10863883933/274877906944), (97504479721/549755813888)), (73/274877906944), by norm_num⟩
  | 6 => ⟨((-10259900309/549755813888), (-46041832175/549755813888)), (35/274877906944), by norm_num⟩
  | 7 => ⟨((8305281847/1099511627776), (74540761887/2199023255552)), (115/2199023255552), by norm_num⟩
  | 8 => ⟨((-23530635355/8796093022208), (-105594940627/8796093022208)), (165/8796093022208), by norm_num⟩
  | 9 => ⟨((3703739449/4398046511104), (1038795121/274877906944)), (105/17592186044416), by norm_num⟩
  | 10 => ⟨((-1049348403/4398046511104), (-75344081883/70368744177664)), (121/70368744177664), by norm_num⟩
  | 11 => ⟨((17297616861/281474976710656), (77623948431/281474976710656)), (127/281474976710656), by norm_num⟩
  | 12 => ⟨((-255249161/17592186044416), (-73308402171/1125899906842624)), (61/562949953421312), by norm_num⟩
  | _ => zero

def term17ValuePoly : ℕ → Disk
  | 20 => ⟨(0, 0), 0, by norm_num⟩
  | 19 => ⟨((666937165097003/81129638414606681695789005144064), 0), (1/162259276829213363391578010288128), by norm_num⟩
  | 18 => ⟨((1581207834572619/10141204801825835211973625643008), (-582935851909/2535301200456458802993406410752)), (607/10141204801825835211973625643008), by norm_num⟩
  | 17 => ⟨((1778687485751647/633825300114114700748351602688), (-1379634030215/316912650057057350374175801344)), (181/158456325028528675187087900672), by norm_num⟩
  | 16 => ⟨((1889650243029779/39614081257132168796771975168), (-3103594737229/39614081257132168796771975168)), (407/19807040628566084398385987584), by norm_num⟩
  | 15 => ⟨((236177422683859/309485009821345068724781056), (-1648427013151/1237940039285380274899124224)), (865/2475880078570760549798248448), by norm_num⟩
  | 14 => ⟨((1771085395564795/154742504910672534362390528), (-206003088989/9671406556917033397649408)), (865/154742504910672534362390528), by norm_num⟩
  | 13 => ⟨((1549454464331429/9671406556917033397649408), (-1544595828769/4835703278458516698824704)), (811/9671406556917033397649408), by norm_num⟩
  | 12 => ⟨((1258701842941315/604462909807314587353088), (-1351094131193/302231454903657293676544)), (355/302231454903657293676544), by norm_num⟩
  | 11 => ⟨((1887650460960869/75557863725914323419136), (-68585224433/1180591620717411303424)), (1153/75557863725914323419136), by norm_num⟩
  | 10 => ⟨((1297432855917265/4722366482869645213696), (-3290689913865/4722366482869645213696)), (433/2361183241434822606848), by norm_num⟩
  | 9 => ⟨((810650439123727/295147905179352825856), (-4522423188891/590295810358705651712)), (1191/590295810358705651712), by norm_num⟩
  | 8 => ⟨((911644788010045/36893488147419103232), (-5649617489571/73786976294838206464)), (1489/73786976294838206464), by norm_num⟩
  | 7 => ⟨((28475739666131/144115188075855872), (-6351131576891/9223372036854775808)), (419/2305843009213693952), by norm_num⟩
  | 6 => ⟨((1593694114680309/1152921504606846976), (-3172637757631/576460752303423488)), (1677/1152921504606846976), by norm_num⟩
  | 5 => ⟨((597161771653009/72057594037927936), (-346595849347/9007199254740992)), (1469/144115188075855872), by norm_num⟩
  | 4 => ⟨((1491247700607161/36028797018963968), (-2076287340691/9007199254740992)), (1103/18014398509481984), by norm_num⟩
  | 3 => ⟨((1488763806189541/9007199254740992), (-5179226893781/4503599627370496)), (2763/9007199254740992), by norm_num⟩
  | 2 => ⟨((2226940194242797/4503599627370496), (-10324042112367/2251799813685248)), (5539/4503599627370496), by norm_num⟩
  | 1 => ⟨((1107270966751903/1125899906842624), (-30800506445393/2251799813685248)), (8347/2251799813685248), by norm_num⟩
  | 0 => ⟨((544352934495647/562949953421312), (-30458580486075/1125899906842624)), (1053/140737488355328), by norm_num⟩
  | _ => zero

def term17ValueSquares : ℕ → Disk
  | 0 => ⟨((544352934495647/562949953421312), (-30458580486075/1125899906842624)), (4016876757574037/536870912000000000000000000), by norm_num⟩
  | 1 => ⟨((2103833097157203/2251799813685248), (-29452383053593/562949953421312)), (33495/2251799813685248), by norm_num⟩
  | 2 => ⟨((1959425783765623/2251799813685248), (-220136436220389/2251799813685248)), (33047/1125899906842624), by norm_num⟩
  | 3 => ⟨((1683493056751623/2251799813685248), (-383107775793429/2251799813685248)), (31987/562949953421312), by norm_num⟩
  | 4 => ⟨((74589703976045/140737488355328), (-143209728639303/562949953421312)), (234851/2251799813685248), by norm_num⟩
  | 5 => ⟨((973570829654613/4503599627370496), (-151799941728759/562949953421312)), (368427/2251799813685248), by norm_num⟩
  | 6 => ⟨((-58500545231635/2251799813685248), (-525048432146455/4503599627370496)), (1431935/9007199254740992), by norm_num⟩
  | _ => zero

def term17Value : CertifiedScalarExp.Data :=
  ⟨⟨((-9126418991/4294967296), (-61660368311/4294967296)), (1/2147483648), by norm_num⟩, -2, term17ValuePoly, term17ValueSquares⟩

set_option maxHeartbeats 5000000 in
-- A bounded Horner table and six outward-rounded squarings.
theorem term17Value_checks : CertifiedScalarExp.Checks term17Value := by
  constructor
  · norm_num [term17Value, CertifiedScalarExp.reduced, term17ValuePoly, term17ValueSquares,
      CertifiedScalarExp.piDisk, CertifiedTaylorModel.mul, CertifiedTaylorModel.add,
      exact, qmul, qadd, size]
  · rfl
  · intro k hk
    interval_cases k <;>
      norm_num [term17Value, CertifiedScalarExp.roundingCheck, CertifiedScalarExp.reduced,
        term17ValuePoly, CertifiedScalarExp.piDisk, CertifiedTaylorModel.mul,
        CertifiedTaylorModel.add, exact, qmul, qadd, size]
  · apply CertifiedScalarExp.disk_ext <;> norm_num [term17Value, term17ValueSquares, term17ValuePoly, inflate]
  · intro k hk
    interval_cases k <;>
      norm_num [term17Value, CertifiedScalarExp.roundingCheck, term17ValueSquares,
        CertifiedTaylorModel.mul, exact, qmul, qadd, size]

set_option maxHeartbeats 5000000 in
theorem S_term17 : Sound J_term17 F_term17 c := by
  apply exp_sound (A_arg17 hcre) S_arg17 term17Value term17Value_checks
  · apply CertifiedScalarExp.disk_ext <;> norm_num [term17Value,J_arg17]
  · rfl
  · intro n hn
    have hlt : n < 12 := by omega
    interval_cases n <;> norm_num [J_term17,J_arg17,sum, CertifiedTaylorModel.get, CertifiedTaylorModel.mul, CertifiedTaylorModel.add, exact, zero, qmul, qadd, size]

def J_log18 : Jet 12 := fun k =>
  match k.val with
  | 0 => ⟨((722592939474041/250000000000000), 0), (3/500000000000000), by norm_num⟩
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

theorem S_log18 : Sound J_log18 F_log18 c := by
  have h := constant_sound (d:=12) (c:=c) RectangleLogInputs.log18_contains
  convert h using 1
  all_goals first | (funext k; fin_cases k <;> rfl) | rfl

def J_negLog18 : Jet 12 := fun k =>
  match k.val with
  | 0 => ⟨((-24828104347/8589934592), 0), (1/34359738368), by norm_num⟩
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
theorem S_negLog18 : Sound J_negLog18 F_negLog18 c := by
  apply sound_round (sound_scale (A_log18 hcre) S_log18)
  intro k
  fin_cases k <;> norm_num [J_negLog18, J_log18, jetScale, sum, CertifiedTaylorModel.get, CertifiedTaylorModel.mul, CertifiedTaylorModel.add, exact, zero, qmul, qadd, size]

def J_arg18 : Jet 12 := fun k =>
  match k.val with
  | 0 => ⟨((-4655269565/2147483648), (-31452164999/2147483648)), (1/4294967296), by norm_num⟩
  | 1 => ⟨((-24828104347/8589934592), 0), (1/34359738368), by norm_num⟩
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
theorem S_arg18 : Sound J_arg18 F_arg18 c := by
  apply sound_round (sound_mul (A_negLog18 hcre) (A_variable hcre) S_negLog18 S_variable)
  intro k
  fin_cases k <;> norm_num [J_arg18, J_negLog18, J_variable, jetMul, sum, CertifiedTaylorModel.get, CertifiedTaylorModel.mul, CertifiedTaylorModel.add, exact, zero, qmul, qadd, size]

def J_term18 : Jet 12 := fun k =>
  match k.val with
  | 0 => ⟨((-502167924546133/9007199254740992), (-225025707791949/2251799813685248)), (180165/2251799813685248), by norm_num⟩
  | 1 => ⟨((44294799403/274877906944), (79395501783/274877906944)), (65/274877906944), by norm_num⟩
  | 2 => ⟨((-4000888663/17179869184), (-57370629015/137438953472)), (49/137438953472), by norm_num⟩
  | 3 => ⟨((30837481595/137438953472), (55274148613/137438953472)), (49/137438953472), by norm_num⟩
  | 4 => ⟨((-2785368309/17179869184), (-79881419047/274877906944)), (73/274877906944), by norm_num⟩
  | 5 => ⟨((12881199833/137438953472), (46177399519/274877906944)), (11/68719476736), by norm_num⟩
  | 6 => ⟨((-6205242701/137438953472), (-22244975237/274877906944)), (45/549755813888), by norm_num⟩
  | 7 => ⟨((1281104161/68719476736), (18370356623/549755813888)), (19/549755813888), by norm_num⟩
  | 8 => ⟨((-29622938287/4398046511104), (-26548579983/2199023255552)), (57/4398046511104), by norm_num⟩
  | 9 => ⟨((38053912983/17592186044416), (2131535161/549755813888)), (19/4398046511104), by norm_num⟩
  | 10 => ⟨((-21997991073/35184372088832), (-19714972897/17592186044416)), (45/35184372088832), by norm_num⟩
  | 11 => ⟨((180631739/1099511627776), (20721309407/70368744177664)), (97/281474976710656), by norm_num⟩
  | 12 => ⟨((-44551925503/1125899906842624), (-79856383329/1125899906842624)), (95/1125899906842624), by norm_num⟩
  | _ => zero

def term18ValuePoly : ℕ → Disk
  | 20 => ⟨(0, 0), 0, by norm_num⟩
  | 19 => ⟨((666937165097003/81129638414606681695789005144064), 0), (1/162259276829213363391578010288128), by norm_num⟩
  | 18 => ⟨((790575996580325/5070602400912917605986812821504), (-2709021946607/10141204801825835211973625643008)), (19/633825300114114700748351602688), by norm_num⟩
  | 17 => ⟨((1778619982415595/633825300114114700748351602688), (-3205493717075/633825300114114700748351602688)), (181/316912650057057350374175801344), by norm_num⟩
  | 16 => ⟨((472393559032185/9903520314283042199192993792), (-901372203613/9903520314283042199192993792)), (407/39614081257132168796771975168), by norm_num⟩
  | 15 => ⟨((944669268384279/1237940039285380274899124224), (-3829983735649/2475880078570760549798248448)), (433/2475880078570760549798248448), by norm_num⟩
  | 14 => ⟨((885502226334373/77371252455336267181195264), (-478628724309/19342813113834066795298816)), (433/154742504910672534362390528), by norm_num⟩
  | 13 => ⟨((96836154757295/604462909807314587353088), (-3588702104009/9671406556917033397649408)), (203/4835703278458516698824704), by norm_num⟩
  | 12 => ⟨((1258635249095107/604462909807314587353088), (-392387659497/75557863725914323419136)), (355/604462909807314587353088), by norm_num⟩
  | 11 => ⟨((1887542050857855/75557863725914323419136), (-5099140635961/75557863725914323419136)), (289/37778931862957161709568), by norm_num⟩
  | 10 => ⟨((648675688909393/2361183241434822606848), (-3822694466057/4722366482869645213696)), (217/2361183241434822606848), by norm_num⟩
  | 9 => ⟨((1621188569128263/590295810358705651712), (-164172087403/18446744073709551616)), (149/147573952589676412928), by norm_num⟩
  | 8 => ⟨((911574387577763/36893488147419103232), (-3281419095237/36893488147419103232)), (373/36893488147419103232), by norm_num⟩
  | 7 => ⟨((1822288368800679/9223372036854775808), (-3688816825513/4611686018427387904)), (839/9223372036854775808), by norm_num⟩
  | 6 => ⟨((796767217659881/576460752303423488), (-3685344490987/576460752303423488)), (105/144115188075855872), by norm_num⟩
  | 5 => ⟨((1194183027767287/144115188075855872), (-6441546255453/144115188075855872)), (23/4503599627370496), by norm_num⟩
  | 4 => ⟨((1491035340398789/36028797018963968), (-9646721545467/36028797018963968)), (1105/36028797018963968), by norm_num⟩
  | 3 => ⟨((744247795374047/4503599627370496), (-12031140291217/9007199254740992)), (173/1125899906842624), by norm_num⟩
  | 2 => ⟨((2226395515284945/4503599627370496), (-23980633927951/4503599627370496)), (347/562949953421312), by norm_num⟩
  | 1 => ⟨((2213704460523097/2251799813685248), (-8941829508935/562949953421312)), (4187/2251799813685248), by norm_num⟩
  | 0 => ⟨((2175655963755177/2251799813685248), (-8840375757525/281474976710656)), (4231/1125899906842624), by norm_num⟩
  | _ => zero

def term18ValueSquares : ℕ → Disk
  | 0 => ⟨((2175655963755177/2251799813685248), (-8840375757525/281474976710656)), (16139988425826671/4294967296000000000000000000), by norm_num⟩
  | 1 => ⟨((2099865672028257/2251799813685248), (-136663063008029/2251799813685248)), (4221/562949953421312), by norm_num⟩
  | 2 => ⟨((1949888716167057/2251799813685248), (-31860522514115/281474976710656)), (8385/562949953421312), by norm_num⟩
  | 3 => ⟨((829802906424377/1125899906842624), (-441420932456959/2251799813685248)), (4105/140737488355328), by norm_num⟩
  | 4 => ⟨((284154812394433/562949953421312), (-650665961482387/2251799813685248)), (61283/1125899906842624), by norm_num⟩
  | 5 => ⟨((771415931203421/4503599627370496), (-41053796854589/140737488355328)), (194565/2251799813685248), by norm_num⟩
  | 6 => ⟨((-502167924546133/9007199254740992), (-225025707791949/2251799813685248)), (180165/2251799813685248), by norm_num⟩
  | _ => zero

def term18Value : CertifiedScalarExp.Data :=
  ⟨⟨((-4655269565/2147483648), (-31452164999/2147483648)), (1/4294967296), by norm_num⟩, -2, term18ValuePoly, term18ValueSquares⟩

set_option maxHeartbeats 5000000 in
-- A bounded Horner table and six outward-rounded squarings.
theorem term18Value_checks : CertifiedScalarExp.Checks term18Value := by
  constructor
  · norm_num [term18Value, CertifiedScalarExp.reduced, term18ValuePoly, term18ValueSquares,
      CertifiedScalarExp.piDisk, CertifiedTaylorModel.mul, CertifiedTaylorModel.add,
      exact, qmul, qadd, size]
  · rfl
  · intro k hk
    interval_cases k <;>
      norm_num [term18Value, CertifiedScalarExp.roundingCheck, CertifiedScalarExp.reduced,
        term18ValuePoly, CertifiedScalarExp.piDisk, CertifiedTaylorModel.mul,
        CertifiedTaylorModel.add, exact, qmul, qadd, size]
  · apply CertifiedScalarExp.disk_ext <;> norm_num [term18Value, term18ValueSquares, term18ValuePoly, inflate]
  · intro k hk
    interval_cases k <;>
      norm_num [term18Value, CertifiedScalarExp.roundingCheck, term18ValueSquares,
        CertifiedTaylorModel.mul, exact, qmul, qadd, size]

set_option maxHeartbeats 5000000 in
theorem S_term18 : Sound J_term18 F_term18 c := by
  apply exp_sound (A_arg18 hcre) S_arg18 term18Value term18Value_checks
  · apply CertifiedScalarExp.disk_ext <;> norm_num [term18Value,J_arg18]
  · rfl
  · intro n hn
    have hlt : n < 12 := by omega
    interval_cases n <;> norm_num [J_term18,J_arg18,sum, CertifiedTaylorModel.get, CertifiedTaylorModel.mul, CertifiedTaylorModel.add, exact, zero, qmul, qadd, size]

def J_log19 : Jet 12 := fun k =>
  match k.val with
  | 0 => ⟨((73610974479161/25000000000000), 0), (3/500000000000000), by norm_num⟩
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

theorem S_log19 : Sound J_log19 F_log19 c := by
  have h := constant_sound (d:=12) (c:=c) RectangleLogInputs.log19_contains
  convert h using 1
  all_goals first | (funext k; fin_cases k <;> rfl) | rfl

def J_negLog19 : Jet 12 := fun k =>
  match k.val with
  | 0 => ⟨((-101170152965/34359738368), 0), (1/34359738368), by norm_num⟩
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
theorem S_negLog19 : Sound J_negLog19 F_negLog19 c := by
  apply sound_round (sound_scale (A_log19 hcre) S_log19)
  intro k
  fin_cases k <;> norm_num [J_negLog19, J_log19, jetScale, sum, CertifiedTaylorModel.get, CertifiedTaylorModel.mul, CertifiedTaylorModel.add, exact, zero, qmul, qadd, size]

def J_arg19 : Jet 12 := fun k =>
  match k.val with
  | 0 => ⟨((-592793865/268435456), (-32040508405/2147483648)), (1/2147483648), by norm_num⟩
  | 1 => ⟨((-101170152965/34359738368), 0), (1/34359738368), by norm_num⟩
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
theorem S_arg19 : Sound J_arg19 F_arg19 c := by
  apply sound_round (sound_mul (A_negLog19 hcre) (A_variable hcre) S_negLog19 S_variable)
  intro k
  fin_cases k <;> norm_num [J_arg19, J_negLog19, J_variable, jetMul, sum, CertifiedTaylorModel.get, CertifiedTaylorModel.mul, CertifiedTaylorModel.add, exact, zero, qmul, qadd, size]

def J_term19 : Jet 12 := fun k =>
  match k.val with
  | 0 => ⟨((-349038512723959/4503599627370496), (-175408324418125/2251799813685248)), (1409725/9007199254740992), by norm_num⟩
  | 1 => ⟨((62727209601/274877906944), (63046766075/274877906944)), (129/274877906944), by norm_num⟩
  | 2 => ⟨((-46174110251/137438953472), (-23204669443/68719476736)), (97/137438953472), by norm_num⟩
  | 3 => ⟨((45318950017/137438953472), (22774911069/68719476736)), (97/137438953472), by norm_num⟩
  | 4 => ⟨((-66719441463/274877906944), (-67059335899/274877906944)), (145/274877906944), by norm_num⟩
  | 5 => ⟨((19645132411/137438953472), (9872606127/68719476736)), (87/274877906944), by norm_num⟩
  | 6 => ⟨((-9640648937/137438953472), (-38759048409/549755813888)), (87/549755813888), by norm_num⟩
  | 7 => ⟨((8110372147/274877906944), (65213515961/2199023255552)), (149/2199023255552), by norm_num⟩
  | 8 => ⟨((-23880495885/2199023255552), (-48004304591/4398046511104)), (7/274877906944), by norm_num⟩
  | 9 => ⟨((62501922601/17592186044416), (15705082845/4398046511104)), (149/17592186044416), by norm_num⟩
  | 10 => ⟨((-9201654859/8796093022208), (-2312132905/2199023255552)), (89/35184372088832), by norm_num⟩
  | 11 => ⟨((39409034531/140737488355328), (9902449819/35184372088832)), (97/140737488355328), by norm_num⟩
  | 12 => ⟨((-19339582901/281474976710656), (-38876212315/562949953421312)), (97/562949953421312), by norm_num⟩
  | _ => zero

def term19ValuePoly : ℕ → Disk
  | 20 => ⟨(0, 0), 0, by norm_num⟩
  | 19 => ⟨((666937165097003/81129638414606681695789005144064), 0), (1/162259276829213363391578010288128), by norm_num⟩
  | 18 => ⟨((790549585858251/5070602400912917605986812821504), (-95809275919/316912650057057350374175801344)), (607/10141204801825835211973625643008), by norm_num⟩
  | 17 => ⟨((889277968809847/316912650057057350374175801344), (-906882208341/158456325028528675187087900672)), (181/158456325028528675187087900672), by norm_num⟩
  | 16 => ⟨((944751056600693/19807040628566084398385987584), (-510021254829/4951760157141521099596496896)), (815/39614081257132168796771975168), by norm_num⟩
  | 15 => ⟨((944630904723911/1237940039285380274899124224), (-2167101281147/1237940039285380274899124224)), (433/1237940039285380274899124224), by norm_num⟩
  | 14 => ⟨((1770927616656449/154742504910672534362390528), (-2166551193605/77371252455336267181195264)), (433/77371252455336267181195264), by norm_num⟩
  | 13 => ⟨((774653163480865/4835703278458516698824704), (-1015278699809/2417851639229258349412352)), (203/2417851639229258349412352), by norm_num⟩
  | 12 => ⟨((157321500411717/75557863725914323419136), (-1776153519207/302231454903657293676544)), (711/604462909807314587353088), by norm_num⟩
  | 11 => ⟨((943719530239303/37778931862957161709568), (-2885154378729/37778931862957161709568)), (1155/75557863725914323419136), by norm_num⟩
  | 10 => ⟨((1297273946294345/4722366482869645213696), (-1081453937797/1180591620717411303424)), (867/4722366482869645213696), by norm_num⟩
  | 9 => ⟨((1621081794488167/590295810358705651712), (-5944884562847/590295810358705651712)), (149/73786976294838206464), by norm_num⟩
  | 8 => ⟨((455753712032197/18446744073709551616), (-1856609874819/18446744073709551616)), (373/18446744073709551616), by norm_num⟩
  | 7 => ⟨((911068535653173/4611686018427387904), (-8348331555961/9223372036854775808)), (1679/9223372036854775808), by norm_num⟩
  | 6 => ⟨((1593382352576887/1152921504606846976), (-8340320181133/1152921504606846976)), (105/72057594037927936), by norm_num⟩
  | 5 => ⟨((149256134293701/18014398509481984), (-7288773861505/144115188075855872)), (1473/144115188075855872), by norm_num⟩
  | 4 => ⟨((1490832654195791/36028797018963968), (-2728791112875/9007199254740992)), (2213/36028797018963968), by norm_num⟩
  | 3 => ⟨((744119586622251/4503599627370496), (-13612498548605/9007199254740992)), (693/2251799813685248), by norm_num⟩
  | 2 => ⟨((139117097152951/281474976710656), (-13565386212769/2251799813685248)), (1391/1125899906842624), by norm_num⟩
  | 1 => ⟨((1106449445565159/1125899906842624), (-20230554755201/1125899906842624)), (2099/562949953421312), by norm_num⟩
  | 0 => ⟨((271744428357273/281474976710656), (-1249767182359/35184372088832)), (8497/1125899906842624), by norm_num⟩
  | _ => zero

def term19ValueSquares : ℕ → Disk
  | 0 => ⟨((271744428357273/281474976710656), (-1249767182359/35184372088832)), (32413486960982921/4294967296000000000000000000), by norm_num⟩
  | 1 => ⟨((523990249167913/562949953421312), (-77220026594165/1125899906842624)), (34021/2251799813685248), by norm_num⟩
  | 2 => ⟨((1940314917421309/2251799813685248), (-143751822803855/1125899906842624)), (68001/2251799813685248), by norm_num⟩
  | 3 => ⟨((204401142263607/281474976710656), (-247734105401087/1125899906842624)), (134555/2251799813685248), by norm_num⟩
  | 4 => ⟨((1078435197782923/2251799813685248), (-719596956196753/2251799813685248)), (63659/562949953421312), by norm_num⟩
  | 5 => ⟨((286527555659371/2251799813685248), (-1378521627124547/4503599627370496)), (813295/4503599627370496), by norm_num⟩
  | 6 => ⟨((-349038512723959/4503599627370496), (-175408324418125/2251799813685248)), (1409725/9007199254740992), by norm_num⟩
  | _ => zero

def term19Value : CertifiedScalarExp.Data :=
  ⟨⟨((-592793865/268435456), (-32040508405/2147483648)), (1/2147483648), by norm_num⟩, -2, term19ValuePoly, term19ValueSquares⟩

set_option maxHeartbeats 5000000 in
-- A bounded Horner table and six outward-rounded squarings.
theorem term19Value_checks : CertifiedScalarExp.Checks term19Value := by
  constructor
  · norm_num [term19Value, CertifiedScalarExp.reduced, term19ValuePoly, term19ValueSquares,
      CertifiedScalarExp.piDisk, CertifiedTaylorModel.mul, CertifiedTaylorModel.add,
      exact, qmul, qadd, size]
  · rfl
  · intro k hk
    interval_cases k <;>
      norm_num [term19Value, CertifiedScalarExp.roundingCheck, CertifiedScalarExp.reduced,
        term19ValuePoly, CertifiedScalarExp.piDisk, CertifiedTaylorModel.mul,
        CertifiedTaylorModel.add, exact, qmul, qadd, size]
  · apply CertifiedScalarExp.disk_ext <;> norm_num [term19Value, term19ValueSquares, term19ValuePoly, inflate]
  · intro k hk
    interval_cases k <;>
      norm_num [term19Value, CertifiedScalarExp.roundingCheck, term19ValueSquares,
        CertifiedTaylorModel.mul, exact, qmul, qadd, size]

set_option maxHeartbeats 5000000 in
theorem S_term19 : Sound J_term19 F_term19 c := by
  apply exp_sound (A_arg19 hcre) S_arg19 term19Value term19Value_checks
  · apply CertifiedScalarExp.disk_ext <;> norm_num [term19Value,J_arg19]
  · rfl
  · intro n hn
    have hlt : n < 12 := by omega
    interval_cases n <;> norm_num [J_term19,J_arg19,sum, CertifiedTaylorModel.get, CertifiedTaylorModel.mul, CertifiedTaylorModel.add, exact, zero, qmul, qadd, size]

def J_log20 : Jet 12 := fun k =>
  match k.val with
  | 0 => ⟨((2995732273553991/1000000000000000), 0), (3/500000000000000), by norm_num⟩
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

theorem S_log20 : Sound J_log20 F_log20 c := by
  have h := constant_sound (d:=12) (c:=c) RectangleLogInputs.log20_contains
  convert h using 1
  all_goals first | (funext k; fin_cases k <;> rfl) | rfl

def J_negLog20 : Jet 12 := fun k =>
  match k.val with
  | 0 => ⟨((-25733144285/8589934592), 0), (1/34359738368), by norm_num⟩
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
theorem S_negLog20 : Sound J_negLog20 F_negLog20 c := by
  apply sound_round (sound_scale (A_log20 hcre) S_log20)
  intro k
  fin_cases k <;> norm_num [J_negLog20, J_log20, jetScale, sum, CertifiedTaylorModel.get, CertifiedTaylorModel.mul, CertifiedTaylorModel.add, exact, zero, qmul, qadd, size]

def J_arg20 : Jet 12 := fun k =>
  match k.val with
  | 0 => ⟨((-9649929107/4294967296), (-8149666691/536870912)), (1/2147483648), by norm_num⟩
  | 1 => ⟨((-25733144285/8589934592), 0), (1/34359738368), by norm_num⟩
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
theorem S_arg20 : Sound J_arg20 F_arg20 c := by
  apply sound_round (sound_mul (A_negLog20 hcre) (A_variable hcre) S_negLog20 S_variable)
  intro k
  fin_cases k <;> norm_num [J_arg20, J_negLog20, J_variable, jetMul, sum, CertifiedTaylorModel.get, CertifiedTaylorModel.mul, CertifiedTaylorModel.add, exact, zero, qmul, qadd, size]

def J_term20 : Jet 12 := fun k =>
  match k.val with
  | 0 => ⟨((-411341102253019/4503599627370496), (-239922343038901/4503599627370496)), (672013/4503599627370496), by norm_num⟩
  | 1 => ⟨((37605829329/137438953472), (21934298895/137438953472)), (125/274877906944), by norm_num⟩
  | 2 => ⟨((-56328498297/137438953472), (-32854643549/137438953472)), (3/4294967296), by norm_num⟩
  | 3 => ⟨((14062091689/34359738368), (32807905339/137438953472)), (49/68719476736), by norm_num⟩
  | 4 => ⟨((-84252523813/274877906944), (-24570925213/137438953472)), (149/274877906944), by norm_num⟩
  | 5 => ⟨((50479600943/274877906944), (29443165461/274877906944)), (91/274877906944), by norm_num⟩
  | 6 => ⟨((-12601947475/137438953472), (-1837580021/34359738368)), (93/549755813888), by norm_num⟩
  | 7 => ⟨((86290424595/2199023255552), (50330493935/2199023255552)), (81/1099511627776), by norm_num⟩
  | 8 => ⟨((-64625752465/4398046511104), (-4711771407/549755813888)), (31/1099511627776), by norm_num⟩
  | 9 => ⟨((86045089939/17592186044416), (3136712371/1099511627776)), (167/17592186044416), by norm_num⟩
  | 10 => ⟨((-25776805291/17592186044416), (-30069601545/35184372088832)), (51/17592186044416), by norm_num⟩
  | 11 => ⟨((28080148189/70368744177664), (32756536655/140737488355328)), (113/140737488355328), by norm_num⟩
  | 12 => ⟨((-56080404117/562949953421312), (-32709938009/562949953421312)), (115/562949953421312), by norm_num⟩
  | _ => zero

def term20ValuePoly : ℕ → Disk
  | 20 => ⟨(0, 0), 0, by norm_num⟩
  | 19 => ⟨((666937165097003/81129638414606681695789005144064), 0), (1/162259276829213363391578010288128), by norm_num⟩
  | 18 => ⟨((790524530142089/5070602400912917605986812821504), (-425557774079/1267650600228229401496703205376)), (19/316912650057057350374175801344), by norm_num⟩
  | 17 => ⟨((1778495006000963/633825300114114700748351602688), (-4027859121429/633825300114114700748351602688)), (181/158456325028528675187087900672), by norm_num⟩
  | 16 => ⟨((472358371751301/9903520314283042199192993792), (-2265217385235/19807040628566084398385987584)), (815/39614081257132168796771975168), by norm_num⟩
  | 15 => ⟨((944594394866941/1237940039285380274899124224), (-1203120390045/618970019642690137449562112)), (433/1237940039285380274899124224), by norm_num⟩
  | 14 => ⟨((1770854479630393/154742504910672534362390528), (-2405619083265/77371252455336267181195264)), (433/77371252455336267181195264), by norm_num⟩
  | 13 => ⟨((1549237636455981/9671406556917033397649408), (-4509214927405/9671406556917033397649408)), (813/9671406556917033397649408), by norm_num⟩
  | 12 => ⟨((1258511774670159/604462909807314587353088), (-3944242490869/604462909807314587353088)), (89/75557863725914323419136), by norm_num⟩
  | 11 => ⟨((1887340955896613/75557863725914323419136), (-6406918579537/75557863725914323419136)), (289/18889465931478580854784), by norm_num⟩
  | 10 => ⟨((648600082081081/2361183241434822606848), (-4803023502007/4722366482869645213696)), (867/4722366482869645213696), by norm_num⟩
  | 9 => ⟨((1620980013499529/590295810358705651712), (-6600639616297/590295810358705651712)), (597/295147905179352825856), by norm_num⟩
  | 8 => ⟨((911443563421091/36893488147419103232), (-4122762474319/36893488147419103232)), (1493/73786976294838206464), by norm_num⟩
  | 7 => ⟨((1821992705437869/9223372036854775808), (-2317241561189/2305843009213693952)), (1681/9223372036854775808), by norm_num⟩
  | 6 => ⟨((1593237139341027/1152921504606846976), (-9259909414827/1152921504606846976)), (841/576460752303423488), by norm_num⟩
  | 5 => ⟨((1193921062101771/144115188075855872), (-1011529805051/18014398509481984)), (1475/144115188075855872), by norm_num⟩
  | 4 => ⟨((1490638741036957/36028797018963968), (-6059004834259/18014398509481984)), (2215/36028797018963968), by norm_num⟩
  | 3 => ⟨((1487993480622581/9007199254740992), (-15111940491255/9007199254740992)), (347/1125899906842624), by norm_num⟩
  | 2 => ⟨((278171540547323/562949953421312), (-7529328985009/1125899906842624)), (697/562949953421312), by norm_num⟩
  | 1 => ⟨((1106061319427943/1125899906842624), (-22455043085771/1125899906842624)), (4209/1125899906842624), by norm_num⟩
  | 0 => ⟨((271538314827443/281474976710656), (-44379888368249/1125899906842624)), (8531/1125899906842624), by norm_num⟩
  | _ => zero

def term20ValueSquares : ℕ → Disk
  | 0 => ⟨((271538314827443/281474976710656), (-44379888368249/1125899906842624)), (32543186668014171/4294967296000000000000000000), by norm_num⟩
  | 1 => ⟨((1046060418923445/1125899906842624), (-85626368926799/1125899906842624)), (17133/1125899906842624), by norm_num⟩
  | 2 => ⟨((1930740944869145/2251799813685248), (-79554456667151/562949953421312)), (68885/2251799813685248), by norm_num⟩
  | 3 => ⟨((805244318110467/1125899906842624), (-272846717369089/1125899906842624)), (137597/2251799813685248), by norm_num⟩
  | 4 => ⟨((509790503739985/1125899906842624), (-390280286091651/1125899906842624)), (131755/1125899906842624), by norm_num⟩
  | 5 => ⟨((95539270709543/1125899906842624), (-706852118691075/2251799813685248)), (842625/4503599627370496), by norm_num⟩
  | 6 => ⟨((-411341102253019/4503599627370496), (-239922343038901/4503599627370496)), (672013/4503599627370496), by norm_num⟩
  | _ => zero

def term20Value : CertifiedScalarExp.Data :=
  ⟨⟨((-9649929107/4294967296), (-8149666691/536870912)), (1/2147483648), by norm_num⟩, -2, term20ValuePoly, term20ValueSquares⟩

set_option maxHeartbeats 5000000 in
-- A bounded Horner table and six outward-rounded squarings.
theorem term20Value_checks : CertifiedScalarExp.Checks term20Value := by
  constructor
  · norm_num [term20Value, CertifiedScalarExp.reduced, term20ValuePoly, term20ValueSquares,
      CertifiedScalarExp.piDisk, CertifiedTaylorModel.mul, CertifiedTaylorModel.add,
      exact, qmul, qadd, size]
  · rfl
  · intro k hk
    interval_cases k <;>
      norm_num [term20Value, CertifiedScalarExp.roundingCheck, CertifiedScalarExp.reduced,
        term20ValuePoly, CertifiedScalarExp.piDisk, CertifiedTaylorModel.mul,
        CertifiedTaylorModel.add, exact, qmul, qadd, size]
  · apply CertifiedScalarExp.disk_ext <;> norm_num [term20Value, term20ValueSquares, term20ValuePoly, inflate]
  · intro k hk
    interval_cases k <;>
      norm_num [term20Value, CertifiedScalarExp.roundingCheck, term20ValueSquares,
        CertifiedTaylorModel.mul, exact, qmul, qadd, size]

set_option maxHeartbeats 5000000 in
theorem S_term20 : Sound J_term20 F_term20 c := by
  apply exp_sound (A_arg20 hcre) S_arg20 term20Value term20Value_checks
  · apply CertifiedScalarExp.disk_ext <;> norm_num [term20Value,J_arg20]
  · rfl
  · intro n hn
    have hlt : n < 12 := by omega
    interval_cases n <;> norm_num [J_term20,J_arg20,sum, CertifiedTaylorModel.get, CertifiedTaylorModel.mul, CertifiedTaylorModel.add, exact, zero, qmul, qadd, size]

def J_log21 : Jet 12 := fun k =>
  match k.val with
  | 0 => ⟨((3044522437723423/1000000000000000), 0), (3/500000000000000), by norm_num⟩
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

theorem S_log21 : Sound J_log21 F_log21 c := by
  have h := constant_sound (d:=12) (c:=c) RectangleLogInputs.log21_contains
  convert h using 1
  all_goals first | (funext k; fin_cases k <;> rfl) | rfl

def J_negLog21 : Jet 12 := fun k =>
  match k.val with
  | 0 => ⟨((-6538062151/2147483648), 0), (1/34359738368), by norm_num⟩
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
theorem S_negLog21 : Sound J_negLog21 F_negLog21 c := by
  apply sound_round (sound_scale (A_log21 hcre) S_log21)
  intro k
  fin_cases k <;> norm_num [J_negLog21, J_log21, jetScale, sum, CertifiedTaylorModel.get, CertifiedTaylorModel.mul, CertifiedTaylorModel.add, exact, zero, qmul, qadd, size]

def J_arg21 : Jet 12 := fun k =>
  match k.val with
  | 0 => ⟨((-4903546613/2147483648), (-16564793403/1073741824)), (1/2147483648), by norm_num⟩
  | 1 => ⟨((-6538062151/2147483648), 0), (1/34359738368), by norm_num⟩
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
theorem S_arg21 : Sound J_arg21 F_arg21 c := by
  apply sound_round (sound_mul (A_negLog21 hcre) (A_variable hcre) S_negLog21 S_variable)
  intro k
  fin_cases k <;> norm_num [J_arg21, J_negLog21, J_variable, jetMul, sum, CertifiedTaylorModel.get, CertifiedTaylorModel.mul, CertifiedTaylorModel.add, exact, zero, qmul, qadd, size]

def J_term21 : Jet 12 := fun k =>
  match k.val with
  | 0 => ⟨((-882214171706089/9007199254740992), (-127223079029913/4503599627370496)), (312691/2251799813685248), by norm_num⟩
  | 1 => ⟨((20491949773/68719476736), (23640961835/274877906944)), (59/137438953472), by norm_num⟩
  | 2 => ⟨((-62388200877/137438953472), (-17993859689/137438953472)), (91/137438953472), by norm_num⟩
  | 3 => ⟨((63314092473/137438953472), (4565225797/34359738368)), (47/68719476736), by norm_num⟩
  | 4 => ⟨((-96380587579/274877906944), (-27797864745/274877906944)), (73/137438953472), by norm_num⟩
  | 5 => ⟨((58686572289/274877906944), (16926244587/274877906944)), (91/274877906944), by norm_num⟩
  | 6 => ⟨((-59557528709/549755813888), (-17177443811/549755813888)), (47/274877906944), by norm_num⟩
  | 7 => ⟨((103613847137/2199023255552), (3735508079/274877906944)), (83/1099511627776), by norm_num⟩
  | 8 => ⟨((-78863670617/4398046511104), (-11372838163/2199023255552)), (1/34359738368), by norm_num⟩
  | 9 => ⟨((53356047715/8796093022208), (15388827097/8796093022208)), (11/1099511627776), by norm_num⟩
  | 10 => ⟨((-64977473783/35184372088832), (-18740651755/35184372088832)), (109/35184372088832), by norm_num⟩
  | 11 => ⟨((71936500683/140737488355328), (20747758097/140737488355328)), (123/140737488355328), by norm_num⟩
  | 12 => ⟨((-73004096807/562949953421312), (-10527835843/281474976710656)), (127/562949953421312), by norm_num⟩
  | _ => zero

def term21ValuePoly : ℕ → Disk
  | 20 => ⟨(0, 0), 0, by norm_num⟩
  | 19 => ⟨((666937165097003/81129638414606681695789005144064), 0), (1/162259276829213363391578010288128), by norm_num⟩
  | 18 => ⟨((1581001394307151/10141204801825835211973625643008), (-1863252725719/5070602400912917605986812821504)), (607/10141204801825835211973625643008), by norm_num⟩
  | 17 => ⟨((889218445933371/316912650057057350374175801344), (-2204302971073/316912650057057350374175801344)), (725/633825300114114700748351602688), by norm_num⟩
  | 16 => ⟨((1889368025929147/39614081257132168796771975168), (-4958669482773/39614081257132168796771975168)), (815/39614081257132168796771975168), by norm_num⟩
  | 15 => ⟨((1889119126647633/2475880078570760549798248448), (-5267356270175/2475880078570760549798248448)), (433/1237940039285380274899124224), by norm_num⟩
  | 14 => ⟨((1770784692137159/154742504910672534362390528), (-5265972576021/154742504910672534362390528)), (433/77371252455336267181195264), by norm_num⟩
  | 13 => ⟨((774586039303463/4835703278458516698824704), (-4935379363683/9671406556917033397649408)), (813/9671406556917033397649408), by norm_num⟩
  | 12 => ⟨((1258454279599795/604462909807314587353088), (-4316987296081/604462909807314587353088)), (89/75557863725914323419136), by norm_num⟩
  | 11 => ⟨((117952954953435/4722366482869645213696), (-7012349361353/75557863725914323419136)), (1157/75557863725914323419136), by norm_num⟩
  | 10 => ⟨((162141211335129/590295810358705651712), (-5256851994553/4722366482869645213696)), (217/1180591620717411303424), by norm_num⟩
  | 9 => ⟨((1620882761947351/590295810358705651712), (-3612128156981/295147905179352825856)), (597/295147905179352825856), by norm_num⟩
  | 8 => ⟨((113922814842207/4611686018427387904), (-9024449576439/73786976294838206464)), (747/36893488147419103232), by norm_num⟩
  | 7 => ⟨((1821854634501003/9223372036854775808), (-39626705375/36028797018963968)), (841/4611686018427387904), by norm_num⟩
  | 6 => ⟨((99568635622871/72057594037927936), (-10134354845869/1152921504606846976)), (421/288230376151711744), by norm_num⟩
  | 5 => ⟨((1193798455986079/144115188075855872), (-8856225106025/144115188075855872)), (369/36028797018963968), by norm_num⟩
  | 4 => ⟨((745226411552957/18014398509481984), (-6630841660259/18014398509481984)), (1109/18014398509481984), by norm_num⟩
  | 3 => ⟨((743878791880331/4503599627370496), (-4134374022691/2251799813685248)), (2781/9007199254740992), by norm_num⟩
  | 2 => ⟨((556222523924739/1125899906842624), (-8239079114717/1125899906842624)), (2793/2251799813685248), by norm_num⟩
  | 1 => ⟨((552843357439871/562949953421312), (-6142288305433/281474976710656)), (1055/281474976710656), by norm_num⟩
  | 0 => ⟨((542676489902273/562949953421312), (-6068442368143/140737488355328)), (2141/281474976710656), by norm_num⟩
  | _ => zero

def term21ValueSquares : ℕ → Disk
  | 0 => ⟨((542676489902273/562949953421312), (-6068442368143/140737488355328)), (8167267919444949/1073741824000000000000000000), by norm_num⟩
  | 1 => ⟨((1044172950089163/1125899906842624), (-46799201008953/562949953421312)), (17251/1125899906842624), by norm_num⟩
  | 2 => ⟨((480298684751901/562949953421312), (-173608540092595/1125899906842624)), (34867/1125899906842624), by norm_num⟩
  | 3 => ⟨((1585589226324199/2251799813685248), (-74059828019709/281474976710656)), (70249/1125899906842624), by norm_num⟩
  | 4 => ⟨((960592616362101/2251799813685248), (-208594857673947/562949953421312)), (67949/562949953421312), by norm_num⟩
  | 5 => ⟨((201216057363815/4503599627370496), (-1423747733701197/4503599627370496)), (866625/4503599627370496), by norm_num⟩
  | 6 => ⟨((-882214171706089/9007199254740992), (-127223079029913/4503599627370496)), (312691/2251799813685248), by norm_num⟩
  | _ => zero

def term21Value : CertifiedScalarExp.Data :=
  ⟨⟨((-4903546613/2147483648), (-16564793403/1073741824)), (1/2147483648), by norm_num⟩, -2, term21ValuePoly, term21ValueSquares⟩

set_option maxHeartbeats 5000000 in
-- A bounded Horner table and six outward-rounded squarings.
theorem term21Value_checks : CertifiedScalarExp.Checks term21Value := by
  constructor
  · norm_num [term21Value, CertifiedScalarExp.reduced, term21ValuePoly, term21ValueSquares,
      CertifiedScalarExp.piDisk, CertifiedTaylorModel.mul, CertifiedTaylorModel.add,
      exact, qmul, qadd, size]
  · rfl
  · intro k hk
    interval_cases k <;>
      norm_num [term21Value, CertifiedScalarExp.roundingCheck, CertifiedScalarExp.reduced,
        term21ValuePoly, CertifiedScalarExp.piDisk, CertifiedTaylorModel.mul,
        CertifiedTaylorModel.add, exact, qmul, qadd, size]
  · apply CertifiedScalarExp.disk_ext <;> norm_num [term21Value, term21ValueSquares, term21ValuePoly, inflate]
  · intro k hk
    interval_cases k <;>
      norm_num [term21Value, CertifiedScalarExp.roundingCheck, term21ValueSquares,
        CertifiedTaylorModel.mul, exact, qmul, qadd, size]

set_option maxHeartbeats 5000000 in
theorem S_term21 : Sound J_term21 F_term21 c := by
  apply exp_sound (A_arg21 hcre) S_arg21 term21Value term21Value_checks
  · apply CertifiedScalarExp.disk_ext <;> norm_num [term21Value,J_arg21]
  · rfl
  · intro n hn
    have hlt : n < 12 := by omega
    interval_cases n <;> norm_num [J_term21,J_arg21,sum, CertifiedTaylorModel.get, CertifiedTaylorModel.mul, CertifiedTaylorModel.add, exact, zero, qmul, qadd, size]

def term16Jet : Jet 12 := J_term16
theorem term16Jet_sound : Sound term16Jet F_term16 (Data.centre ⟨11,by norm_num [Data.count]⟩) := S_term16

def term17Jet : Jet 12 := J_term17
theorem term17Jet_sound : Sound term17Jet F_term17 (Data.centre ⟨11,by norm_num [Data.count]⟩) := S_term17

def term18Jet : Jet 12 := J_term18
theorem term18Jet_sound : Sound term18Jet F_term18 (Data.centre ⟨11,by norm_num [Data.count]⟩) := S_term18

def term19Jet : Jet 12 := J_term19
theorem term19Jet_sound : Sound term19Jet F_term19 (Data.centre ⟨11,by norm_num [Data.count]⟩) := S_term19

def term20Jet : Jet 12 := J_term20
theorem term20Jet_sound : Sound term20Jet F_term20 (Data.centre ⟨11,by norm_num [Data.count]⟩) := S_term20

def term21Jet : Jet 12 := J_term21
theorem term21Jet_sound : Sound term21Jet F_term21 (Data.centre ⟨11,by norm_num [Data.count]⟩) := S_term21

end Reinmann.XiRectangle.Tile011Terms2
