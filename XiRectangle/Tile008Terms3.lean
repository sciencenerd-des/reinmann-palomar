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
namespace Reinmann.XiRectangle.Tile008Terms3
open CertifiedTaylorModel CertifiedTaylorComposition RectangleTaylor RectangleModel
open scoped Topology
set_option maxRecDepth 30000
set_option linter.style.longLine false
set_option linter.style.whitespace false

def c : ℂ := Data.centre ⟨8,by norm_num [Data.count]⟩
theorem hc : c ∈ XiAdaptiveTiles.quarter (141/10) := Data.centre_mem_quarter _
theorem hcre : -2<c.re := by linarith [hc.1]

def J_variable : Jet 12 := fun k =>
  match k.val with
  | 0 => ⟨((3/4), (2397/640)), 0, by norm_num⟩
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
  have h := variable_sound 12 ((3/4), (2397/640))
  have he : value ((3/4), (2397/640))=c := by norm_num [c,Data.centre,Data.coordinate,value]
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
  | 0 => ⟨((-53103704991/17179869184), 0), (1/34359738368), by norm_num⟩
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
  | 0 => ⟨((-4978472343/2147483648), (-49722492525/4294967296)), (1/4294967296), by norm_num⟩
  | 1 => ⟨((-53103704991/17179869184), 0), (1/34359738368), by norm_num⟩
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
  | 0 => ⟨((486926014895121/9007199254740992), (370515063158217/4503599627370496)), (221375/4503599627370496), by norm_num⟩
  | 1 => ⟨((-11483070249/68719476736), (-17475552213/68719476736)), (11/68719476736), by norm_num⟩
  | 2 => ⟨((35494657635/137438953472), (27008836893/68719476736)), (9/34359738368), by norm_num⟩
  | 3 => ⟨((-18285915603/68719476736), (-27828487151/68719476736)), (39/137438953472), by norm_num⟩
  | 4 => ⟨((14130635357/68719476736), (21504758799/68719476736)), (1/4294967296), by norm_num⟩
  | 5 => ⟨((-34942715025/274877906944), (-26588848959/137438953472)), (41/274877906944), by norm_num⟩
  | 6 => ⟨((18001569263/274877906944), (54791507279/549755813888)), (11/137438953472), by norm_num⟩
  | 7 => ⟨((-31796351325/1099511627776), (-48389392881/1099511627776)), (5/137438953472), by norm_num⟩
  | 8 => ⟨((1535685497/137438953472), (18696708461/1099511627776)), (1/68719476736), by norm_num⟩
  | 9 => ⟨((-2109719585/549755813888), (-12842737687/2199023255552)), (23/4398046511104), by norm_num⟩
  | 10 => ⟨((10433972483/8796093022208), (63515915853/35184372088832)), (59/35184372088832), by norm_num⟩
  | 11 => ⟨((-46911784585/140737488355328), (-71392869951/140737488355328)), (17/35184372088832), by norm_num⟩
  | 12 => ⟨((24167719619/281474976710656), (36779731981/281474976710656)), (9/70368744177664), by norm_num⟩
  | _ => zero

def term22ValuePoly : ℕ → Disk
  | 20 => ⟨(0, 0), 0, by norm_num⟩
  | 19 => ⟨((666937165097003/81129638414606681695789005144064), 0), (1/162259276829213363391578010288128), by norm_num⟩
  | 18 => ⟨((790477973085591/5070602400912917605986812821504), (644434988913/5070602400912917605986812821504)), (19/633825300114114700748351602688), by norm_num⟩
  | 17 => ⟨((889196145982507/316912650057057350374175801344), (1524697231747/633825300114114700748351602688)), (181/316912650057057350374175801344), by norm_num⟩
  | 16 => ⟨((944659187387355/19807040628566084398385987584), (1714938258809/39614081257132168796771975168)), (203/19807040628566084398385987584), by norm_num⟩
  | 15 => ⟨((472266765041949/618970019642690137449562112), (910845523579/1237940039285380274899124224)), (27/154742504910672534362390528), by norm_num⟩
  | 14 => ⟨((885366699423697/77371252455336267181195264), (455301632283/38685626227668133590597632)), (27/9671406556917033397649408), by norm_num⟩
  | 13 => ⟨((193640601511605/1208925819614629174706176), (213358311515/1208925819614629174706176)), (405/9671406556917033397649408), by norm_num⟩
  | 12 => ⟨((629206870852325/302231454903657293676544), (1492993744589/604462909807314587353088)), (355/604462909807314587353088), by norm_num⟩
  | 11 => ⟨((943591470943237/37778931862957161709568), (2425150677227/75557863725914323419136)), (9/1180591620717411303424), by norm_num⟩
  | 10 => ⟨((324270695229377/1180591620717411303424), (1818019779515/4722366482869645213696)), (27/295147905179352825856), by norm_num⟩
  | 9 => ⟨((810410220638685/295147905179352825856), (156150482393/36893488147419103232)), (595/590295810358705651712), by norm_num⟩
  | 8 => ⟨((455672600641417/18446744073709551616), (1560478386279/36893488147419103232)), (743/73786976294838206464), by norm_num⟩
  | 7 => ⟨((1821775153645957/9223372036854775808), (3508255845665/9223372036854775808)), (209/2305843009213693952), by norm_num⟩
  | 6 => ⟨((796512141272821/576460752303423488), (1752366729405/576460752303423488)), (209/288230376151711744), by norm_num⟩
  | 5 => ⟨((596870041111085/72057594037927936), (3062683579729/144115188075855872)), (733/144115188075855872), by norm_num⟩
  | 4 => ⟨((46574305648629/1125899906842624), (4586120184479/36028797018963968)), (1099/36028797018963968), by norm_num⟩
  | 3 => ⟨((371921401092383/2251799813685248), (357427583755/562949953421312)), (1375/9007199254740992), by norm_num⟩
  | 2 => ⟨((556202818593641/1125899906842624), (5698178282933/2251799813685248)), (2753/4503599627370496), by norm_num⟩
  | 1 => ⟨((1105708439234561/1125899906842624), (8495785360313/1125899906842624)), (1035/562949953421312), by norm_num⟩
  | 0 => ⟨((542858156892781/562949953421312), (33573385543669/2251799813685248)), (4161/1125899906842624), by norm_num⟩
  | _ => zero

def term22ValueSquares : ℕ → Disk
  | 0 => ⟨((542858156892781/562949953421312), (33573385543669/2251799813685248)), (15872959617232921/4294967296000000000000000000), by norm_num⟩
  | 1 => ⟨((523358299349527/562949953421312), (32375144692919/1125899906842624)), (16299/2251799813685248), by norm_num⟩
  | 2 => ⟨((972171221745403/1125899906842624), (60196472402939/1125899906842624)), (7811/562949953421312), by norm_num⟩
  | 3 => ⟨((836214003907713/1125899906842624), (207909345280401/2251799813685248)), (28649/1125899906842624), by norm_num⟩
  | 4 => ⟨((38216501428303/70368744177664), (150796654735/1099511627776)), (95693/2251799813685248), by norm_num⟩
  | 5 => ⟨((310901544371247/1125899906842624), (335446126471707/2251799813685248)), (260377/4503599627370496), by norm_num⟩
  | 6 => ⟨((486926014895121/9007199254740992), (370515063158217/4503599627370496)), (221375/4503599627370496), by norm_num⟩
  | _ => zero

def term22Value : CertifiedScalarExp.Data :=
  ⟨⟨((-4978472343/2147483648), (-49722492525/4294967296)), (1/4294967296), by norm_num⟩, -2, term22ValuePoly, term22ValueSquares⟩

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
  | 0 => ⟨((-53867380457/17179869184), 0), (1/34359738368), by norm_num⟩
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
  | 0 => ⟨((-20200267671/8589934592), (-25218771671/2147483648)), (1/4294967296), by norm_num⟩
  | 1 => ⟨((-53867380457/17179869184), 0), (1/34359738368), by norm_num⟩
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
  | 0 => ⟨((583223482550387/9007199254740992), (78596976559591/1125899906842624)), (391335/9007199254740992), by norm_num⟩
  | 1 => ⟨((-55807307621/274877906944), (-235023847/1073741824)), (5/34359738368), by norm_num⟩
  | 2 => ⟨((43745872563/137438953472), (5895327303/17179869184)), (33/137438953472), by norm_num⟩
  | 3 => ⟨((-5715205433/17179869184), (-49292705759/137438953472)), (9/34359738368), by norm_num⟩
  | 4 => ⟨((8959996789/34359738368), (38639248449/137438953472)), (15/68719476736), by norm_num⟩
  | 5 => ⟨((-44950428971/274877906944), (-6057657001/34359738368)), (39/274877906944), by norm_num⟩
  | 6 => ⟨((46980603347/549755813888), (25324997985/274877906944)), (43/549755813888), by norm_num⟩
  | 7 => ⟨((-42087831445/1099511627776), (-11343769243/274877906944)), (41/1099511627776), by norm_num⟩
  | 8 => ⟨((65983076029/4398046511104), (71136645697/4398046511104)), (67/4398046511104), by norm_num⟩
  | 9 => ⟨((-45975456275/8796093022208), (-6195792809/1099511627776)), (3/549755813888), by norm_num⟩
  | 10 => ⟨((28831155445/17592186044416), (31082996025/17592186044416)), (31/17592186044416), by norm_num⟩
  | 11 => ⟨((-32872698595/70368744177664), (-70880403091/140737488355328)), (73/140737488355328), by norm_num⟩
  | 12 => ⟨((8589346359/70368744177664), (18520424493/140737488355328)), (5/35184372088832), by norm_num⟩
  | _ => zero

def term23ValuePoly : ℕ → Disk
  | 20 => ⟨(0, 0), 0, by norm_num⟩
  | 19 => ⟨((666937165097003/81129638414606681695789005144064), 0), (1/162259276829213363391578010288128), by norm_num⟩
  | 18 => ⟨((1580912518633433/10141204801825835211973625643008), (268000927671/2535301200456458802993406410752)), (305/10141204801825835211973625643008), by norm_num⟩
  | 17 => ⟨((444585325913195/158456325028528675187087900672), (634040341817/316912650057057350374175801344)), (181/316912650057057350374175801344), by norm_num⟩
  | 16 => ⟨((3689962980647/77371252455336267181195264), (1426299305037/39614081257132168796771975168)), (203/19807040628566084398385987584), by norm_num⟩
  | 15 => ⟨((1889006191241157/2475880078570760549798248448), (757539783527/1237940039285380274899124224)), (27/154742504910672534362390528), by norm_num⟩
  | 14 => ⟨((1770672578033469/154742504910672534362390528), (1514670861875/154742504910672534362390528)), (27/9671406556917033397649408), by norm_num⟩
  | 13 => ⟨((1549067843670177/9671406556917033397649408), (354892458381/2417851639229258349412352)), (405/9671406556917033397649408), by norm_num⟩
  | 12 => ⟨((629181972696079/302231454903657293676544), (1241689673383/604462909807314587353088)), (355/604462909807314587353088), by norm_num⟩
  | 11 => ⟨((943551059270491/37778931862957161709568), (1008466228345/37778931862957161709568)), (9/1180591620717411303424), by norm_num⟩
  | 10 => ⟨((1297022247042759/4722366482869645213696), (755994047789/2361183241434822606848)), (27/295147905179352825856), by norm_num⟩
  | 9 => ⟨((1620737342974009/590295810358705651712), (1038914262819/295147905179352825856)), (297/295147905179352825856), by norm_num⟩
  | 8 => ⟨((1822586733118299/73786976294838206464), (2595554170991/73786976294838206464)), (743/73786976294838206464), by norm_num⟩
  | 7 => ⟨((1821658804863399/9223372036854775808), (1458809776567/4611686018427387904)), (209/2305843009213693952), by norm_num⟩
  | 6 => ⟨((24889191912287/18014398509481984), (2914648795279/1152921504606846976)), (209/288230376151711744), by norm_num⟩
  | 5 => ⟨((1193638973516625/144115188075855872), (159186219569/9007199254740992)), (183/36028797018963968), by norm_num⟩
  | 4 => ⟨((93139181165643/2251799813685248), (1906901345857/18014398509481984)), (549/18014398509481984), by norm_num⟩
  | 3 => ⟨((1487498364103919/9007199254740992), (2377804421225/4503599627370496)), (1373/9007199254740992), by norm_num⟩
  | 2 => ⟨((556110215946899/1125899906842624), (2369092977757/1125899906842624)), (2749/4503599627370496), by norm_num⟩
  | 1 => ⟨((2210871377605085/2251799813685248), (7063874984563/1125899906842624)), (4133/2251799813685248), by norm_num⟩
  | 0 => ⟨((2170381728447469/2251799813685248), (27910101687555/2251799813685248)), (8301/2251799813685248), by norm_num⟩
  | _ => zero

def term23ValueSquares : ℕ → Disk
  | 0 => ⟨((2170381728447469/2251799813685248), (27910101687555/2251799813685248)), (31665810591887717/8589934592000000000000000000), by norm_num⟩
  | 1 => ⟨((1045780767184293/1125899906842624), (53801918246581/2251799813685248)), (1013/140737488355328), by norm_num⟩
  | 2 => ⟨((1941440344329975/2251799813685248), (99946737712557/2251799813685248)), (30885/2251799813685248), by norm_num⟩
  | 3 => ⟨((834710358657611/1125899906842624), (172342699115657/2251799813685248)), (55999/2251799813685248), by norm_num⟩
  | 4 => ⟨((1224470980371173/2251799813685248), (63885002261999/562949953421312)), (91605/2251799813685248), by norm_num⟩
  | 5 => ⟨((636836577049001/2251799813685248), (277912204718563/2251799813685248)), (240833/4503599627370496), by norm_num⟩
  | 6 => ⟨((583223482550387/9007199254740992), (78596976559591/1125899906842624)), (391335/9007199254740992), by norm_num⟩
  | _ => zero

def term23Value : CertifiedScalarExp.Data :=
  ⟨⟨((-20200267671/8589934592), (-25218771671/2147483648)), (1/4294967296), by norm_num⟩, -2, term23ValuePoly, term23ValueSquares⟩

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
  | 0 => ⟨((-54598549065/17179869184), 0), (1/34359738368), by norm_num⟩
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
  | 0 => ⟨((-20474455899/8589934592), (-25561078537/2147483648)), (1/4294967296), by norm_num⟩
  | 1 => ⟨((-54598549065/17179869184), 0), (1/34359738368), by norm_num⟩
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
  | 0 => ⟨((654406823596029/9007199254740992), (511637856849341/9007199254740992)), (42997/1125899906842624), by norm_num⟩
  | 1 => ⟨((-31734315679/137438953472), (-12405492025/68719476736)), (35/274877906944), by norm_num⟩
  | 2 => ⟨((12606670437/34359738368), (39425321447/137438953472)), (15/68719476736), by norm_num⟩
  | 3 => ⟨((-26709784847/68719476736), (-10441316153/34359738368)), (17/68719476736), by norm_num⟩
  | 4 => ⟨((10610641755/34359738368), (16591532397/68719476736)), (29/137438953472), by norm_num⟩
  | 5 => ⟨((-53953905075/274877906944), (-10545756617/68719476736)), (39/274877906944), by norm_num⟩
  | 6 => ⟨((57156138229/549755813888), (44686642947/549755813888)), (11/137438953472), by norm_num⟩
  | 7 => ⟨((-51898652579/1099511627776), (-40576159081/1099511627776)), (21/549755813888), by norm_num⟩
  | 8 => ⟨((41234177905/2199023255552), (32238304447/2199023255552)), (35/2199023255552), by norm_num⟩
  | 9 => ⟨((-29120986007/4398046511104), (-45535585303/8796093022208)), (51/8796093022208), by norm_num⟩
  | 10 => ⟨((37019224449/17592186044416), (14471454129/8796093022208)), (67/35184372088832), by norm_num⟩
  | 11 => ⟨((-21390743283/35184372088832), (-4181005475/8796093022208)), (5/8796093022208), by norm_num⟩
  | 12 => ⟨((2832538901/17592186044416), (35433227905/281474976710656)), (11/70368744177664), by norm_num⟩
  | _ => zero

def term24ValuePoly : ℕ → Disk
  | 20 => ⟨(0, 0), 0, by norm_num⟩
  | 19 => ⟨((666937165097003/81129638414606681695789005144064), 0), (1/162259276829213363391578010288128), by norm_num⟩
  | 18 => ⟨((1580870939646257/10141204801825835211973625643008), (864368643409/10141204801825835211973625643008)), (19/633825300114114700748351602688), by norm_num⟩
  | 17 => ⟨((444573105574015/158456325028528675187087900672), (63900863969/39614081257132168796771975168)), (181/316912650057057350374175801344), by norm_num⟩
  | 16 => ⟨((118075380170595/2475880078570760549798248448), (1149977741837/39614081257132168796771975168)), (407/39614081257132168796771975168), by norm_num⟩
  | 15 => ⟨((1888947828984801/2475880078570760549798248448), (1221554369475/2475880078570760549798248448)), (27/154742504910672534362390528), by norm_num⟩
  | 14 => ⟨((1770614256600873/154742504910672534362390528), (1221220410339/154742504910672534362390528)), (433/154742504910672534362390528), by norm_num⟩
  | 13 => ⟨((1549013210677679/9671406556917033397649408), (572269714529/4835703278458516698824704)), (405/9671406556917033397649408), by norm_num⟩
  | 12 => ⟨((1258316184846495/604462909807314587353088), (250279359131/151115727451828646838272)), (177/302231454903657293676544), by norm_num⟩
  | 11 => ⟨((1887024588825465/75557863725914323419136), (101634458005/4722366482869645213696)), (9/1180591620717411303424), by norm_num⟩
  | 10 => ⟨((81060260670121/295147905179352825856), (609516176981/2361183241434822606848)), (27/295147905179352825856), by norm_num⟩
  | 9 => ⟨((810328801620923/295147905179352825856), (1675225694625/590295810358705651712)), (297/295147905179352825856), by norm_num⟩
  | 8 => ⟨((911243615536689/36893488147419103232), (1046308708111/36893488147419103232)), (371/36893488147419103232), by norm_num⟩
  | 7 => ⟨((910773551051093/4611686018427387904), (1176125489505/4611686018427387904)), (835/9223372036854775808), by norm_num⟩
  | 6 => ⟨((796398437727269/576460752303423488), (293727982585/144115188075855872)), (835/1152921504606846976), by norm_num⟩
  | 5 => ⟨((596770912307169/72057594037927936), (1026684332861/72057594037927936)), (731/144115188075855872), by norm_num⟩
  | 4 => ⟨((1490081838013323/36028797018963968), (3074606802659/36028797018963968)), (1097/36028797018963968), by norm_num⟩
  | 3 => ⟨((1487318194447533/9007199254740992), (3833746146323/9007199254740992)), (343/2251799813685248), by norm_num⟩
  | 2 => ⟨((2224083978476935/4503599627370496), (7639029020435/4503599627370496)), (1373/2251799813685248), by norm_num⟩
  | 1 => ⟨((2210344634357101/2251799813685248), (11387642996107/2251799813685248)), (2063/1125899906842624), by norm_num⟩
  | 0 => ⟨((2169362280483341/2251799813685248), (5623306135965/562949953421312)), (1035/281474976710656), by norm_num⟩
  | _ => zero

def term24ValueSquares : ℕ → Disk
  | 0 => ⟨((2169362280483341/2251799813685248), (5623306135965/562949953421312)), (3948212743663699/1073741824000000000000000000), by norm_num⟩
  | 1 => ⟨((2089718069179681/2251799813685248), (21669756163641/1125899906842624)), (2015/281474976710656), by norm_num⟩
  | 2 => ⟨((1938468627983209/2251799813685248), (80439976475117/2251799813685248)), (30541/2251799813685248), by norm_num⟩
  | 3 => ⟨((416465754311511/562949953421312), (138493990349461/2251799813685248)), (27383/1125899906842624), by norm_num⟩
  | 4 => ⟨((611936947084763/1125899906842624), (204913434339813/2251799813685248)), (10971/281474976710656), by norm_num⟩
  | 5 => ⟨((80817452355705/281474976710656), (222744669689517/2251799813685248)), (222759/4503599627370496), by norm_num⟩
  | 6 => ⟨((654406823596029/9007199254740992), (511637856849341/9007199254740992)), (42997/1125899906842624), by norm_num⟩
  | _ => zero

def term24Value : CertifiedScalarExp.Data :=
  ⟨⟨((-20474455899/8589934592), (-25561078537/2147483648)), (1/4294967296), by norm_num⟩, -2, term24ValuePoly, term24ValueSquares⟩

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
  | 0 => ⟨((-55299865591/17179869184), 0), (1/34359738368), by norm_num⟩
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
  | 0 => ⟨((-20737449597/8589934592), (-103557638923/8589934592)), (1/4294967296), by norm_num⟩
  | 1 => ⟨((-55299865591/17179869184), 0), (1/34359738368), by norm_num⟩
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
  | 0 => ⟨((1405684444626559/18014398509481984), (49220473030347/1125899906842624)), (601609/18014398509481984), by norm_num⟩
  | 1 => ⟨((-34520902071/137438953472), (-19340160001/137438953472)), (1/8589934592), by norm_num⟩
  | 2 => ⟨((55559248565/137438953472), (15563393369/68719476736)), (7/34359738368), by norm_num⟩
  | 3 => ⟨((-29806387009/68719476736), (-33397753779/137438953472)), (1/4294967296), by norm_num⟩
  | 4 => ⟨((47971529285/137438953472), (26875805561/137438953472)), (27/137438953472), by norm_num⟩
  | 5 => ⟨((-61765758359/274877906944), (-17301976159/137438953472)), (37/274877906944), by norm_num⟩
  | 6 => ⟨((66272102129/549755813888), (37128608521/549755813888)), (21/274877906944), by norm_num⟩
  | 7 => ⟨((-60949047831/1099511627776), (-17073197197/549755813888)), (41/1099511627776), by norm_num⟩
  | 8 => ⟨((49046854153/2199023255552), (27478250855/2199023255552)), (35/2199023255552), by norm_num⟩
  | 9 => ⟨((-35083496249/4398046511104), (-39310701061/8796093022208)), (13/2199023255552), by norm_num⟩
  | 10 => ⟨((45171767171/17592186044416), (25307253061/17592186044416)), (35/17592186044416), by norm_num⟩
  | 11 => ⟨((-52873567023/70368744177664), (-29622147299/70368744177664)), (21/35184372088832), by norm_num⟩
  | 12 => ⟨((56731148889/281474976710656), (31783337941/281474976710656)), (47/281474976710656), by norm_num⟩
  | _ => zero

def term25ValuePoly : ℕ → Disk
  | 20 => ⟨(0, 0), 0, by norm_num⟩
  | 19 => ⟨((666937165097003/81129638414606681695789005144064), 0), (1/162259276829213363391578010288128), by norm_num⟩
  | 18 => ⟨((1580831058241879/10141204801825835211973625643008), (332605440481/5070602400912917605986812821504)), (19/633825300114114700748351602688), by norm_num⟩
  | 17 => ⟨((1778245478360823/633825300114114700748351602688), (786801351967/633825300114114700748351602688)), (181/316912650057057350374175801344), by norm_num⟩
  | 16 => ⟨((472288323633197/9903520314283042199192993792), (884966411993/39614081257132168796771975168)), (203/19807040628566084398385987584), by norm_num⟩
  | 15 => ⟨((1888891772075149/2475880078570760549798248448), (470022676509/1237940039285380274899124224)), (27/154742504910672534362390528), by norm_num⟩
  | 14 => ⟨((885279117016701/77371252455336267181195264), (469892538755/77371252455336267181195264)), (27/9671406556917033397649408), by norm_num⟩
  | 13 => ⟨((774480362994435/4835703278458516698824704), (55048254247/604462909807314587353088)), (405/9671406556917033397649408), by norm_num⟩
  | 12 => ⟨((1258270297189045/604462909807314587353088), (385199615181/302231454903657293676544)), (177/302231454903657293676544), by norm_num⟩
  | 11 => ⟨((1886950089668257/75557863725914323419136), (1251380872547/75557863725914323419136)), (575/75557863725914323419136), by norm_num⟩
  | 10 => ⟨((162113544506967/590295810358705651712), (469041376175/2361183241434822606848)), (27/295147905179352825856), by norm_num⟩
  | 9 => ⟨((1620580954999901/590295810358705651712), (1289128268609/590295810358705651712)), (593/590295810358705651712), by norm_num⟩
  | 8 => ⟨((1822391565997631/73786976294838206464), (1610307848861/73786976294838206464)), (371/36893488147419103232), by norm_num⟩
  | 7 => ⟨((910719839159929/4611686018427387904), (1810081688181/9223372036854775808)), (835/9223372036854775808), by norm_num⟩
  | 6 => ⟨((1592689700569347/1152921504606846976), (1808190300701/1152921504606846976)), (417/576460752303423488), by norm_num⟩
  | 5 => ⟨((1193448326066747/144115188075855872), (1580041332073/144115188075855872)), (731/144115188075855872), by norm_num⟩
  | 4 => ⟨((744971073908691/18014398509481984), (1182909100993/18014398509481984)), (1097/36028797018963968), by norm_num⟩
  | 3 => ⟨((743572277282293/4503599627370496), (2949860858689/9007199254740992)), (1371/9007199254740992), by norm_num⟩
  | 2 => ⟨((2223739605399157/4503599627370496), (183673278563/140737488355328)), (2743/4503599627370496), by norm_num⟩
  | 1 => ⟨((1104917649981791/1125899906842624), (2190270224539/562949953421312)), (4119/2251799813685248), by norm_num⟩
  | 0 => ⟨((271046533095571/281474976710656), (17302444828729/2251799813685248)), (8261/2251799813685248), by norm_num⟩
  | _ => zero

def term25ValueSquares : ℕ → Disk
  | 0 => ⟨((271046533095571/281474976710656), (17302444828729/2251799813685248)), (31513222701262717/8589934592000000000000000000), by norm_num⟩
  | 1 => ⟨((2087902696958097/2251799813685248), (33322803609113/2251799813685248)), (8019/1125899906842624), by norm_num⟩
  | 2 => ⟨((1935441701450335/2251799813685248), (61794810624669/2251799813685248)), (30217/2251799813685248), by norm_num⟩
  | 3 => ⟨((830916664605403/1125899906842624), (1659786938671/35184372088832)), (53603/2251799813685248), by norm_num⟩
  | 4 => ⟨((1221425615605693/2251799813685248), (78395295704247/1125899906842624)), (5261/140737488355328), by norm_num⟩
  | 5 => ⟨((1303221748208757/4503599627370496), (340186624882755/4503599627370496)), (206081/4503599627370496), by norm_num⟩
  | 6 => ⟨((1405684444626559/18014398509481984), (49220473030347/1125899906842624)), (601609/18014398509481984), by norm_num⟩
  | _ => zero

def term25Value : CertifiedScalarExp.Data :=
  ⟨⟨((-20737449597/8589934592), (-103557638923/8589934592)), (1/4294967296), by norm_num⟩, -2, term25ValuePoly, term25ValueSquares⟩

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
  | 0 => ⟨((-6996709039/2147483648), 0), (1/34359738368), by norm_num⟩
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
  | 0 => ⟨((-20990127117/8589934592), (-104819447291/8589934592)), (1/4294967296), by norm_num⟩
  | 1 => ⟨((-6996709039/2147483648), 0), (1/34359738368), by norm_num⟩
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
  | 0 => ⟨((365541023089359/4503599627370496), (139170835000687/4503599627370496)), (261665/9007199254740992), by norm_num⟩
  | 1 => ⟨((-36345457209/137438953472), (-3459411741/34359738368)), (7/68719476736), by norm_num⟩
  | 2 => ⟨((59208504153/137438953472), (11271097417/68719476736)), (25/137438953472), by norm_num⟩
  | 3 => ⟨((-64302340801/137438953472), (-24481548983/137438953472)), (29/137438953472), by norm_num⟩
  | 4 => ⟨((6546976061/17179869184), (19940812497/137438953472)), (13/68719476736), by norm_num⟩
  | 5 => ⟨((-17064544031/68719476736), (-25987636865/274877906944)), (9/68719476736), by norm_num⟩
  | 6 => ⟨((37065287887/274877906944), (7055852475/137438953472)), (41/549755813888), by norm_num⟩
  | 7 => ⟨((-34503510327/549755813888), (-1642046323/68719476736)), (5/137438953472), by norm_num⟩
  | 8 => ⟨((56207883773/2199023255552), (21399781761/2199023255552)), (17/1099511627776), by norm_num⟩
  | 9 => ⟨((-81391427347/8796093022208), (-7746950541/2199023255552)), (51/8796093022208), by norm_num⟩
  | 10 => ⟨((53036225533/17592186044416), (10096125095/8796093022208)), (35/17592186044416), by norm_num⟩
  | 11 => ⟨((-31417662327/35184372088832), (-23923018341/70368744177664)), (43/70368744177664), by norm_num⟩
  | 12 => ⟨((68241184573/281474976710656), (25981167745/281474976710656)), (49/281474976710656), by norm_num⟩
  | _ => zero

def term26ValuePoly : ℕ → Disk
  | 20 => ⟨(0, 0), 0, by norm_num⟩
  | 19 => ⟨((666937165097003/81129638414606681695789005144064), 0), (1/162259276829213363391578010288128), by norm_num⟩
  | 18 => ⟨((1580792741223529/10141204801825835211973625643008), (473865270195/10141204801825835211973625643008)), (19/633825300114114700748351602688), by norm_num⟩
  | 17 => ⟨((1778200322074341/633825300114114700748351602688), (280226718927/316912650057057350374175801344)), (361/633825300114114700748351602688), by norm_num⟩
  | 16 => ⟨((472275628373969/9903520314283042199192993792), (630376804807/39614081257132168796771975168)), (407/39614081257132168796771975168), by norm_num⟩
  | 15 => ⟨((1888837842625531/2475880078570760549798248448), (41850530213/154742504910672534362390528)), (431/2475880078570760549798248448), by norm_num⟩
  | 14 => ⟨((1770504333140313/154742504910672534362390528), (83677604901/19342813113834066795298816)), (27/9671406556917033397649408), by norm_num⟩
  | 13 => ⟨((387227556056629/2417851639229258349412352), (627382738691/9671406556917033397649408)), (405/9671406556917033397649408), by norm_num⟩
  | 12 => ⟨((1258226138453443/604462909807314587353088), (548760681457/604462909807314587353088)), (177/302231454903657293676544), by norm_num⟩
  | 11 => ⟨((1886878388508313/75557863725914323419136), (891362756079/75557863725914323419136)), (9/1180591620717411303424), by norm_num⟩
  | 10 => ⟨((81053414364615/295147905179352825856), (167048890307/1180591620717411303424)), (27/295147905179352825856), by norm_num⟩
  | 9 => ⟨((405126790512377/147573952589676412928), (918238655533/590295810358705651712)), (593/590295810358705651712), by norm_num⟩
  | 8 => ⟨((455574861397101/18446744073709551616), (573501768101/36893488147419103232)), (371/36893488147419103232), by norm_num⟩
  | 7 => ⟨((1821336208722003/9223372036854775808), (20145110791/144115188075855872)), (417/4611686018427387904), by norm_num⟩
  | 6 => ⟨((1592586437987629/1152921504606846976), (321980909685/288230376151711744)), (417/576460752303423488), by norm_num⟩
  | 5 => ⟨((596679101886253/72057594037927936), (1125401233803/144115188075855872)), (365/72057594037927936), by norm_num⟩
  | 4 => ⟨((1489807428236469/36028797018963968), (842521388553/18014398509481984)), (137/4503599627370496), by norm_num⟩
  | 3 => ⟨((1486976964444043/9007199254740992), (2100960934291/9007199254740992)), (685/4503599627370496), by norm_num⟩
  | 2 => ⟨((2223406843650195/4503599627370496), (4185937533695/4503599627370496)), (685/1125899906842624), by norm_num⟩
  | 1 => ⟨((1104671085088123/1125899906842624), (6239096524531/2251799813685248)), (4113/2251799813685248), by norm_num⟩
  | 0 => ⟨((1083704928551513/1125899906842624), (769991066967/140737488355328)), (4121/1125899906842624), by norm_num⟩
  | _ => zero

def term26ValueSquares : ℕ → Disk
  | 0 => ⟨((1083704928551513/1125899906842624), (769991066967/140737488355328)), (15720371726607921/4294967296000000000000000000), by norm_num⟩
  | 1 => ⟨((2086115151640077/2251799813685248), (23716299728357/2251799813685248)), (15957/2251799813685248), by norm_num⟩
  | 2 => ⟨((966185789825657/1125899906842624), (5492820887483/281474976710656)), (29903/2251799813685248), by norm_num⟩
  | 3 => ⟨((828699103259287/1125899906842624), (75418220824639/2251799813685248)), (52491/2251799813685248), by norm_num⟩
  | 4 => ⟨((76085829496215/140737488355328), (27755136840741/562949953421312)), (80787/2251799813685248), by norm_num⟩
  | 5 => ⟨((326332765542451/1125899906842624), (60020187484859/1125899906842624)), (95317/2251799813685248), by norm_num⟩
  | 6 => ⟨((365541023089359/4503599627370496), (139170835000687/4503599627370496)), (261665/9007199254740992), by norm_num⟩
  | _ => zero

def term26Value : CertifiedScalarExp.Data :=
  ⟨⟨((-20990127117/8589934592), (-104819447291/8589934592)), (1/4294967296), by norm_num⟩, -2, term26ValuePoly, term26ValueSquares⟩

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
  | 0 => ⟨((-28311023105/8589934592), 0), (1/34359738368), by norm_num⟩
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
  | 0 => ⟨((-21233267329/8589934592), (-106033628723/8589934592)), (1/4294967296), by norm_num⟩
  | 1 => ⟨((-28311023105/8589934592), 0), (1/34359738368), by norm_num⟩
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
  | 0 => ⟨((1483418284806519/18014398509481984), (335510664276563/18014398509481984)), (452853/18014398509481984), by norm_num⟩
  | 1 => ⟨((-18650454219/68719476736), (-263640503/4294967296)), (25/274877906944), by norm_num⟩
  | 2 => ⟨((61468854583/137438953472), (13902657427/137438953472)), (11/68719476736), by norm_num⟩
  | 3 => ⟨((-8441304877/17179869184), (-15273630295/137438953472)), (13/68719476736), by norm_num⟩
  | 4 => ⟨((27821163811/68719476736), (12584848451/137438953472)), (45/274877906944), by norm_num⟩
  | 5 => ⟨((-73355213875/274877906944), (-16591042991/274877906944)), (31/274877906944), by norm_num⟩
  | 6 => ⟨((80588939401/549755813888), (35599851/1073741824)), (9/137438953472), by norm_num⟩
  | 7 => ⟨((-75887999277/1099511627776), (-8581946613/549755813888)), (9/274877906944), by norm_num⟩
  | 8 => ⟨((31264308213/1099511627776), (14142348015/2199023255552)), (1/68719476736), by norm_num⟩
  | 9 => ⟨((-45796470933/4398046511104), (-20715943093/8796093022208)), (49/8796093022208), by norm_num⟩
  | 10 => ⟨((30187539447/8796093022208), (213363653/274877906944)), (17/8796093022208), by norm_num⟩
  | 11 => ⟨((-72358694839/70368744177664), (-16365656283/70368744177664)), (43/70368744177664), by norm_num⟩
  | 12 => ⟨((39747075671/140737488355328), (17979511105/281474976710656)), (49/281474976710656), by norm_num⟩
  | _ => zero

def term27ValuePoly : ℕ → Disk
  | 20 => ⟨(0, 0), 0, by norm_num⟩
  | 19 => ⟨((666937165097003/81129638414606681695789005144064), 0), (1/162259276829213363391578010288128), by norm_num⟩
  | 18 => ⟨((1580755870480279/10141204801825835211973625643008), (36217749543/1267650600228229401496703205376)), (19/633825300114114700748351602688), by norm_num⟩
  | 17 => ⟨((1778156820460937/633825300114114700748351602688), (342669779321/633825300114114700748351602688)), (361/633825300114114700748351602688), by norm_num⟩
  | 16 => ⟨((1889053590443867/39614081257132168796771975168), (192710562783/19807040628566084398385987584)), (203/19807040628566084398385987584), by norm_num⟩
  | 15 => ⟨((1888785882673967/2475880078570760549798248448), (409406740915/2475880078570760549798248448)), (431/2475880078570760549798248448), by norm_num⟩
  | 14 => ⟨((110653274785173/9671406556917033397649408), (409290689963/154742504910672534362390528)), (431/154742504910672534362390528), by norm_num⟩
  | 13 => ⟨((1548861558507247/9671406556917033397649408), (383586764149/9671406556917033397649408)), (405/9671406556917033397649408), by norm_num⟩
  | 12 => ⟨((1258183580756943/604462909807314587353088), (167757606607/302231454903657293676544)), (177/302231454903657293676544), by norm_num⟩
  | 11 => ⟨((1886809278735835/75557863725914323419136), (544981322341/75557863725914323419136)), (575/75557863725914323419136), by norm_num⟩
  | 10 => ⟨((648401419073945/2361183241434822606848), (102133516495/1180591620717411303424)), (27/295147905179352825856), by norm_num⟩
  | 9 => ⟨((1620436014469941/590295810358705651712), (561406419261/590295810358705651712)), (593/590295810358705651712), by norm_num⟩
  | 8 => ⟨((1822210609997341/73786976294838206464), (701266505485/73786976294838206464)), (741/73786976294838206464), by norm_num⟩
  | 7 => ⟨((1821236404485167/9223372036854775808), (788249570961/9223372036854775808)), (417/4611686018427387904), by norm_num⟩
  | 6 => ⟨((1592486803262643/1152921504606846976), (49212899749/72057594037927936)), (417/576460752303423488), by norm_num⟩
  | 5 => ⟨((596635606878329/72057594037927936), (688033239631/144115188075855872)), (365/72057594037927936), by norm_num⟩
  | 4 => ⟨((1489677323120385/36028797018963968), (1030158178987/36028797018963968)), (547/18014398509481984), by norm_num⟩
  | 3 => ⟨((1486814996025375/9007199254740992), (321098524029/2251799813685248)), (171/1125899906842624), by norm_num⟩
  | 2 => ⟨((2223084888314023/4503599627370496), (1279452252043/2251799813685248)), (2737/4503599627370496), by norm_num⟩
  | 1 => ⟨((2208864165015807/2251799813685248), (953435614153/562949953421312)), (4107/2251799813685248), by norm_num⟩
  | 0 => ⟨((2166473403416133/2251799813685248), (3764797580403/1125899906842624)), (8223/2251799813685248), by norm_num⟩
  | _ => zero

def term27ValueSquares : ℕ → Disk
  | 0 => ⟨((2166473403416133/2251799813685248), (3764797580403/1125899906842624)), (31368264205168967/8589934592000000000000000000), by norm_num⟩
  | 1 => ⟨((2084355049850027/2251799813685248), (7244279689179/1125899906842624)), (15879/2251799813685248), by norm_num⟩
  | 2 => ⟨((60289635165945/70368744177664), (26822368242325/2251799813685248)), (14801/1125899906842624), by norm_num⟩
  | 3 => ⟨((1652614414918597/2251799813685248), (45961053149779/2251799813685248)), (25715/1125899906842624), by norm_num⟩
  | 4 => ⟨((37872788044431/70368744177664), (67462390305341/2251799813685248)), (38795/1125899906842624), by norm_num⟩
  | 5 => ⟨((162561214926403/562949953421312), (36308574763735/1125899906842624)), (11021/281474976710656), by norm_num⟩
  | 6 => ⟨((1483418284806519/18014398509481984), (335510664276563/18014398509481984)), (452853/18014398509481984), by norm_num⟩
  | _ => zero

def term27Value : CertifiedScalarExp.Data :=
  ⟨⟨((-21233267329/8589934592), (-106033628723/8589934592)), (1/4294967296), by norm_num⟩, -2, term27ValuePoly, term27ValueSquares⟩

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
theorem term22Jet_sound : Sound term22Jet F_term22 (Data.centre ⟨8,by norm_num [Data.count]⟩) := S_term22

def term23Jet : Jet 12 := J_term23
theorem term23Jet_sound : Sound term23Jet F_term23 (Data.centre ⟨8,by norm_num [Data.count]⟩) := S_term23

def term24Jet : Jet 12 := J_term24
theorem term24Jet_sound : Sound term24Jet F_term24 (Data.centre ⟨8,by norm_num [Data.count]⟩) := S_term24

def term25Jet : Jet 12 := J_term25
theorem term25Jet_sound : Sound term25Jet F_term25 (Data.centre ⟨8,by norm_num [Data.count]⟩) := S_term25

def term26Jet : Jet 12 := J_term26
theorem term26Jet_sound : Sound term26Jet F_term26 (Data.centre ⟨8,by norm_num [Data.count]⟩) := S_term26

def term27Jet : Jet 12 := J_term27
theorem term27Jet_sound : Sound term27Jet F_term27 (Data.centre ⟨8,by norm_num [Data.count]⟩) := S_term27

end Reinmann.XiRectangle.Tile008Terms3
