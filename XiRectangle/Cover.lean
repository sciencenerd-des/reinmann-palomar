/-
Copyright (c) 2026 Biswajit Mondal. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Biswajit Mondal
-/
module

public import Reinmann.RationalBallCover
public import XiRectangle.Data

@[expose] public section

noncomputable section
namespace Reinmann.XiRectangle.Cover
open RationalBallCover

theorem cell5 : ∀ z ∈ rectangle ((1/2)) (1) (0) ((141/320)),
    ∃ i:Fin Data.count, ‖z-Data.centre i‖≤(Data.radius i:ℝ) := by
  intro z hz
  refine ⟨⟨0,by norm_num [Data.count]⟩,?_⟩
  apply rectangle_ball (c:=Data.centre ⟨0,by norm_num [Data.count]⟩) (r:=(Data.radius ⟨0,by norm_num [Data.count]⟩:ℝ))
    (by norm_num [Data.radius]) ?_ ?_ ?_ ?_ hz
  all_goals norm_num [Data.centre,Data.coordinate,Data.radius,CertifiedTaylorModel.value]

theorem cell6 : ∀ z ∈ rectangle ((1/2)) (1) ((141/320)) ((141/160)),
    ∃ i:Fin Data.count, ‖z-Data.centre i‖≤(Data.radius i:ℝ) := by
  intro z hz
  refine ⟨⟨1,by norm_num [Data.count]⟩,?_⟩
  apply rectangle_ball (c:=Data.centre ⟨1,by norm_num [Data.count]⟩) (r:=(Data.radius ⟨1,by norm_num [Data.count]⟩:ℝ))
    (by norm_num [Data.radius]) ?_ ?_ ?_ ?_ hz
  all_goals norm_num [Data.centre,Data.coordinate,Data.radius,CertifiedTaylorModel.value]

theorem cell4 : ∀ z ∈ rectangle ((1/2)) (1) (0) ((141/160)),
    ∃ i:Fin Data.count, ‖z-Data.centre i‖≤(Data.radius i:ℝ) :=
  split_y cell5 cell6

theorem cell8 : ∀ z ∈ rectangle ((1/2)) (1) ((141/160)) ((423/320)),
    ∃ i:Fin Data.count, ‖z-Data.centre i‖≤(Data.radius i:ℝ) := by
  intro z hz
  refine ⟨⟨2,by norm_num [Data.count]⟩,?_⟩
  apply rectangle_ball (c:=Data.centre ⟨2,by norm_num [Data.count]⟩) (r:=(Data.radius ⟨2,by norm_num [Data.count]⟩:ℝ))
    (by norm_num [Data.radius]) ?_ ?_ ?_ ?_ hz
  all_goals norm_num [Data.centre,Data.coordinate,Data.radius,CertifiedTaylorModel.value]

theorem cell9 : ∀ z ∈ rectangle ((1/2)) (1) ((423/320)) ((141/80)),
    ∃ i:Fin Data.count, ‖z-Data.centre i‖≤(Data.radius i:ℝ) := by
  intro z hz
  refine ⟨⟨3,by norm_num [Data.count]⟩,?_⟩
  apply rectangle_ball (c:=Data.centre ⟨3,by norm_num [Data.count]⟩) (r:=(Data.radius ⟨3,by norm_num [Data.count]⟩:ℝ))
    (by norm_num [Data.radius]) ?_ ?_ ?_ ?_ hz
  all_goals norm_num [Data.centre,Data.coordinate,Data.radius,CertifiedTaylorModel.value]

theorem cell7 : ∀ z ∈ rectangle ((1/2)) (1) ((141/160)) ((141/80)),
    ∃ i:Fin Data.count, ‖z-Data.centre i‖≤(Data.radius i:ℝ) :=
  split_y cell8 cell9

theorem cell3 : ∀ z ∈ rectangle ((1/2)) (1) (0) ((141/80)),
    ∃ i:Fin Data.count, ‖z-Data.centre i‖≤(Data.radius i:ℝ) :=
  split_y cell4 cell7

theorem cell12 : ∀ z ∈ rectangle ((1/2)) (1) ((141/80)) ((141/64)),
    ∃ i:Fin Data.count, ‖z-Data.centre i‖≤(Data.radius i:ℝ) := by
  intro z hz
  refine ⟨⟨4,by norm_num [Data.count]⟩,?_⟩
  apply rectangle_ball (c:=Data.centre ⟨4,by norm_num [Data.count]⟩) (r:=(Data.radius ⟨4,by norm_num [Data.count]⟩:ℝ))
    (by norm_num [Data.radius]) ?_ ?_ ?_ ?_ hz
  all_goals norm_num [Data.centre,Data.coordinate,Data.radius,CertifiedTaylorModel.value]

theorem cell13 : ∀ z ∈ rectangle ((1/2)) (1) ((141/64)) ((423/160)),
    ∃ i:Fin Data.count, ‖z-Data.centre i‖≤(Data.radius i:ℝ) := by
  intro z hz
  refine ⟨⟨5,by norm_num [Data.count]⟩,?_⟩
  apply rectangle_ball (c:=Data.centre ⟨5,by norm_num [Data.count]⟩) (r:=(Data.radius ⟨5,by norm_num [Data.count]⟩:ℝ))
    (by norm_num [Data.radius]) ?_ ?_ ?_ ?_ hz
  all_goals norm_num [Data.centre,Data.coordinate,Data.radius,CertifiedTaylorModel.value]

theorem cell11 : ∀ z ∈ rectangle ((1/2)) (1) ((141/80)) ((423/160)),
    ∃ i:Fin Data.count, ‖z-Data.centre i‖≤(Data.radius i:ℝ) :=
  split_y cell12 cell13

theorem cell15 : ∀ z ∈ rectangle ((1/2)) (1) ((423/160)) ((987/320)),
    ∃ i:Fin Data.count, ‖z-Data.centre i‖≤(Data.radius i:ℝ) := by
  intro z hz
  refine ⟨⟨6,by norm_num [Data.count]⟩,?_⟩
  apply rectangle_ball (c:=Data.centre ⟨6,by norm_num [Data.count]⟩) (r:=(Data.radius ⟨6,by norm_num [Data.count]⟩:ℝ))
    (by norm_num [Data.radius]) ?_ ?_ ?_ ?_ hz
  all_goals norm_num [Data.centre,Data.coordinate,Data.radius,CertifiedTaylorModel.value]

theorem cell16 : ∀ z ∈ rectangle ((1/2)) (1) ((987/320)) ((141/40)),
    ∃ i:Fin Data.count, ‖z-Data.centre i‖≤(Data.radius i:ℝ) := by
  intro z hz
  refine ⟨⟨7,by norm_num [Data.count]⟩,?_⟩
  apply rectangle_ball (c:=Data.centre ⟨7,by norm_num [Data.count]⟩) (r:=(Data.radius ⟨7,by norm_num [Data.count]⟩:ℝ))
    (by norm_num [Data.radius]) ?_ ?_ ?_ ?_ hz
  all_goals norm_num [Data.centre,Data.coordinate,Data.radius,CertifiedTaylorModel.value]

theorem cell14 : ∀ z ∈ rectangle ((1/2)) (1) ((423/160)) ((141/40)),
    ∃ i:Fin Data.count, ‖z-Data.centre i‖≤(Data.radius i:ℝ) :=
  split_y cell15 cell16

theorem cell10 : ∀ z ∈ rectangle ((1/2)) (1) ((141/80)) ((141/40)),
    ∃ i:Fin Data.count, ‖z-Data.centre i‖≤(Data.radius i:ℝ) :=
  split_y cell11 cell14

theorem cell2 : ∀ z ∈ rectangle ((1/2)) (1) (0) ((141/40)),
    ∃ i:Fin Data.count, ‖z-Data.centre i‖≤(Data.radius i:ℝ) :=
  split_y cell3 cell10

theorem cell20 : ∀ z ∈ rectangle ((1/2)) (1) ((141/40)) ((1269/320)),
    ∃ i:Fin Data.count, ‖z-Data.centre i‖≤(Data.radius i:ℝ) := by
  intro z hz
  refine ⟨⟨8,by norm_num [Data.count]⟩,?_⟩
  apply rectangle_ball (c:=Data.centre ⟨8,by norm_num [Data.count]⟩) (r:=(Data.radius ⟨8,by norm_num [Data.count]⟩:ℝ))
    (by norm_num [Data.radius]) ?_ ?_ ?_ ?_ hz
  all_goals norm_num [Data.centre,Data.coordinate,Data.radius,CertifiedTaylorModel.value]

theorem cell21 : ∀ z ∈ rectangle ((1/2)) (1) ((1269/320)) ((141/32)),
    ∃ i:Fin Data.count, ‖z-Data.centre i‖≤(Data.radius i:ℝ) := by
  intro z hz
  refine ⟨⟨9,by norm_num [Data.count]⟩,?_⟩
  apply rectangle_ball (c:=Data.centre ⟨9,by norm_num [Data.count]⟩) (r:=(Data.radius ⟨9,by norm_num [Data.count]⟩:ℝ))
    (by norm_num [Data.radius]) ?_ ?_ ?_ ?_ hz
  all_goals norm_num [Data.centre,Data.coordinate,Data.radius,CertifiedTaylorModel.value]

theorem cell19 : ∀ z ∈ rectangle ((1/2)) (1) ((141/40)) ((141/32)),
    ∃ i:Fin Data.count, ‖z-Data.centre i‖≤(Data.radius i:ℝ) :=
  split_y cell20 cell21

theorem cell23 : ∀ z ∈ rectangle ((1/2)) (1) ((141/32)) ((1551/320)),
    ∃ i:Fin Data.count, ‖z-Data.centre i‖≤(Data.radius i:ℝ) := by
  intro z hz
  refine ⟨⟨10,by norm_num [Data.count]⟩,?_⟩
  apply rectangle_ball (c:=Data.centre ⟨10,by norm_num [Data.count]⟩) (r:=(Data.radius ⟨10,by norm_num [Data.count]⟩:ℝ))
    (by norm_num [Data.radius]) ?_ ?_ ?_ ?_ hz
  all_goals norm_num [Data.centre,Data.coordinate,Data.radius,CertifiedTaylorModel.value]

theorem cell24 : ∀ z ∈ rectangle ((1/2)) (1) ((1551/320)) ((423/80)),
    ∃ i:Fin Data.count, ‖z-Data.centre i‖≤(Data.radius i:ℝ) := by
  intro z hz
  refine ⟨⟨11,by norm_num [Data.count]⟩,?_⟩
  apply rectangle_ball (c:=Data.centre ⟨11,by norm_num [Data.count]⟩) (r:=(Data.radius ⟨11,by norm_num [Data.count]⟩:ℝ))
    (by norm_num [Data.radius]) ?_ ?_ ?_ ?_ hz
  all_goals norm_num [Data.centre,Data.coordinate,Data.radius,CertifiedTaylorModel.value]

theorem cell22 : ∀ z ∈ rectangle ((1/2)) (1) ((141/32)) ((423/80)),
    ∃ i:Fin Data.count, ‖z-Data.centre i‖≤(Data.radius i:ℝ) :=
  split_y cell23 cell24

theorem cell18 : ∀ z ∈ rectangle ((1/2)) (1) ((141/40)) ((423/80)),
    ∃ i:Fin Data.count, ‖z-Data.centre i‖≤(Data.radius i:ℝ) :=
  split_y cell19 cell22

theorem cell27 : ∀ z ∈ rectangle ((1/2)) (1) ((423/80)) ((1833/320)),
    ∃ i:Fin Data.count, ‖z-Data.centre i‖≤(Data.radius i:ℝ) := by
  intro z hz
  refine ⟨⟨12,by norm_num [Data.count]⟩,?_⟩
  apply rectangle_ball (c:=Data.centre ⟨12,by norm_num [Data.count]⟩) (r:=(Data.radius ⟨12,by norm_num [Data.count]⟩:ℝ))
    (by norm_num [Data.radius]) ?_ ?_ ?_ ?_ hz
  all_goals norm_num [Data.centre,Data.coordinate,Data.radius,CertifiedTaylorModel.value]

theorem cell28 : ∀ z ∈ rectangle ((1/2)) (1) ((1833/320)) ((987/160)),
    ∃ i:Fin Data.count, ‖z-Data.centre i‖≤(Data.radius i:ℝ) := by
  intro z hz
  refine ⟨⟨13,by norm_num [Data.count]⟩,?_⟩
  apply rectangle_ball (c:=Data.centre ⟨13,by norm_num [Data.count]⟩) (r:=(Data.radius ⟨13,by norm_num [Data.count]⟩:ℝ))
    (by norm_num [Data.radius]) ?_ ?_ ?_ ?_ hz
  all_goals norm_num [Data.centre,Data.coordinate,Data.radius,CertifiedTaylorModel.value]

theorem cell26 : ∀ z ∈ rectangle ((1/2)) (1) ((423/80)) ((987/160)),
    ∃ i:Fin Data.count, ‖z-Data.centre i‖≤(Data.radius i:ℝ) :=
  split_y cell27 cell28

theorem cell30 : ∀ z ∈ rectangle ((1/2)) (1) ((987/160)) ((423/64)),
    ∃ i:Fin Data.count, ‖z-Data.centre i‖≤(Data.radius i:ℝ) := by
  intro z hz
  refine ⟨⟨14,by norm_num [Data.count]⟩,?_⟩
  apply rectangle_ball (c:=Data.centre ⟨14,by norm_num [Data.count]⟩) (r:=(Data.radius ⟨14,by norm_num [Data.count]⟩:ℝ))
    (by norm_num [Data.radius]) ?_ ?_ ?_ ?_ hz
  all_goals norm_num [Data.centre,Data.coordinate,Data.radius,CertifiedTaylorModel.value]

theorem cell31 : ∀ z ∈ rectangle ((1/2)) (1) ((423/64)) ((141/20)),
    ∃ i:Fin Data.count, ‖z-Data.centre i‖≤(Data.radius i:ℝ) := by
  intro z hz
  refine ⟨⟨15,by norm_num [Data.count]⟩,?_⟩
  apply rectangle_ball (c:=Data.centre ⟨15,by norm_num [Data.count]⟩) (r:=(Data.radius ⟨15,by norm_num [Data.count]⟩:ℝ))
    (by norm_num [Data.radius]) ?_ ?_ ?_ ?_ hz
  all_goals norm_num [Data.centre,Data.coordinate,Data.radius,CertifiedTaylorModel.value]

theorem cell29 : ∀ z ∈ rectangle ((1/2)) (1) ((987/160)) ((141/20)),
    ∃ i:Fin Data.count, ‖z-Data.centre i‖≤(Data.radius i:ℝ) :=
  split_y cell30 cell31

theorem cell25 : ∀ z ∈ rectangle ((1/2)) (1) ((423/80)) ((141/20)),
    ∃ i:Fin Data.count, ‖z-Data.centre i‖≤(Data.radius i:ℝ) :=
  split_y cell26 cell29

theorem cell17 : ∀ z ∈ rectangle ((1/2)) (1) ((141/40)) ((141/20)),
    ∃ i:Fin Data.count, ‖z-Data.centre i‖≤(Data.radius i:ℝ) :=
  split_y cell18 cell25

theorem cell1 : ∀ z ∈ rectangle ((1/2)) (1) (0) ((141/20)),
    ∃ i:Fin Data.count, ‖z-Data.centre i‖≤(Data.radius i:ℝ) :=
  split_y cell2 cell17

theorem cell36 : ∀ z ∈ rectangle ((1/2)) (1) ((141/20)) ((2397/320)),
    ∃ i:Fin Data.count, ‖z-Data.centre i‖≤(Data.radius i:ℝ) := by
  intro z hz
  refine ⟨⟨16,by norm_num [Data.count]⟩,?_⟩
  apply rectangle_ball (c:=Data.centre ⟨16,by norm_num [Data.count]⟩) (r:=(Data.radius ⟨16,by norm_num [Data.count]⟩:ℝ))
    (by norm_num [Data.radius]) ?_ ?_ ?_ ?_ hz
  all_goals norm_num [Data.centre,Data.coordinate,Data.radius,CertifiedTaylorModel.value]

theorem cell37 : ∀ z ∈ rectangle ((1/2)) (1) ((2397/320)) ((1269/160)),
    ∃ i:Fin Data.count, ‖z-Data.centre i‖≤(Data.radius i:ℝ) := by
  intro z hz
  refine ⟨⟨17,by norm_num [Data.count]⟩,?_⟩
  apply rectangle_ball (c:=Data.centre ⟨17,by norm_num [Data.count]⟩) (r:=(Data.radius ⟨17,by norm_num [Data.count]⟩:ℝ))
    (by norm_num [Data.radius]) ?_ ?_ ?_ ?_ hz
  all_goals norm_num [Data.centre,Data.coordinate,Data.radius,CertifiedTaylorModel.value]

theorem cell35 : ∀ z ∈ rectangle ((1/2)) (1) ((141/20)) ((1269/160)),
    ∃ i:Fin Data.count, ‖z-Data.centre i‖≤(Data.radius i:ℝ) :=
  split_y cell36 cell37

theorem cell39 : ∀ z ∈ rectangle ((1/2)) (1) ((1269/160)) ((2679/320)),
    ∃ i:Fin Data.count, ‖z-Data.centre i‖≤(Data.radius i:ℝ) := by
  intro z hz
  refine ⟨⟨18,by norm_num [Data.count]⟩,?_⟩
  apply rectangle_ball (c:=Data.centre ⟨18,by norm_num [Data.count]⟩) (r:=(Data.radius ⟨18,by norm_num [Data.count]⟩:ℝ))
    (by norm_num [Data.radius]) ?_ ?_ ?_ ?_ hz
  all_goals norm_num [Data.centre,Data.coordinate,Data.radius,CertifiedTaylorModel.value]

theorem cell40 : ∀ z ∈ rectangle ((1/2)) (1) ((2679/320)) ((141/16)),
    ∃ i:Fin Data.count, ‖z-Data.centre i‖≤(Data.radius i:ℝ) := by
  intro z hz
  refine ⟨⟨19,by norm_num [Data.count]⟩,?_⟩
  apply rectangle_ball (c:=Data.centre ⟨19,by norm_num [Data.count]⟩) (r:=(Data.radius ⟨19,by norm_num [Data.count]⟩:ℝ))
    (by norm_num [Data.radius]) ?_ ?_ ?_ ?_ hz
  all_goals norm_num [Data.centre,Data.coordinate,Data.radius,CertifiedTaylorModel.value]

theorem cell38 : ∀ z ∈ rectangle ((1/2)) (1) ((1269/160)) ((141/16)),
    ∃ i:Fin Data.count, ‖z-Data.centre i‖≤(Data.radius i:ℝ) :=
  split_y cell39 cell40

theorem cell34 : ∀ z ∈ rectangle ((1/2)) (1) ((141/20)) ((141/16)),
    ∃ i:Fin Data.count, ‖z-Data.centre i‖≤(Data.radius i:ℝ) :=
  split_y cell35 cell38

theorem cell43 : ∀ z ∈ rectangle ((1/2)) (1) ((141/16)) ((2961/320)),
    ∃ i:Fin Data.count, ‖z-Data.centre i‖≤(Data.radius i:ℝ) := by
  intro z hz
  refine ⟨⟨20,by norm_num [Data.count]⟩,?_⟩
  apply rectangle_ball (c:=Data.centre ⟨20,by norm_num [Data.count]⟩) (r:=(Data.radius ⟨20,by norm_num [Data.count]⟩:ℝ))
    (by norm_num [Data.radius]) ?_ ?_ ?_ ?_ hz
  all_goals norm_num [Data.centre,Data.coordinate,Data.radius,CertifiedTaylorModel.value]

theorem cell44 : ∀ z ∈ rectangle ((1/2)) (1) ((2961/320)) ((1551/160)),
    ∃ i:Fin Data.count, ‖z-Data.centre i‖≤(Data.radius i:ℝ) := by
  intro z hz
  refine ⟨⟨21,by norm_num [Data.count]⟩,?_⟩
  apply rectangle_ball (c:=Data.centre ⟨21,by norm_num [Data.count]⟩) (r:=(Data.radius ⟨21,by norm_num [Data.count]⟩:ℝ))
    (by norm_num [Data.radius]) ?_ ?_ ?_ ?_ hz
  all_goals norm_num [Data.centre,Data.coordinate,Data.radius,CertifiedTaylorModel.value]

theorem cell42 : ∀ z ∈ rectangle ((1/2)) (1) ((141/16)) ((1551/160)),
    ∃ i:Fin Data.count, ‖z-Data.centre i‖≤(Data.radius i:ℝ) :=
  split_y cell43 cell44

theorem cell46 : ∀ z ∈ rectangle ((1/2)) (1) ((1551/160)) ((3243/320)),
    ∃ i:Fin Data.count, ‖z-Data.centre i‖≤(Data.radius i:ℝ) := by
  intro z hz
  refine ⟨⟨22,by norm_num [Data.count]⟩,?_⟩
  apply rectangle_ball (c:=Data.centre ⟨22,by norm_num [Data.count]⟩) (r:=(Data.radius ⟨22,by norm_num [Data.count]⟩:ℝ))
    (by norm_num [Data.radius]) ?_ ?_ ?_ ?_ hz
  all_goals norm_num [Data.centre,Data.coordinate,Data.radius,CertifiedTaylorModel.value]

theorem cell47 : ∀ z ∈ rectangle ((1/2)) (1) ((3243/320)) ((423/40)),
    ∃ i:Fin Data.count, ‖z-Data.centre i‖≤(Data.radius i:ℝ) := by
  intro z hz
  refine ⟨⟨23,by norm_num [Data.count]⟩,?_⟩
  apply rectangle_ball (c:=Data.centre ⟨23,by norm_num [Data.count]⟩) (r:=(Data.radius ⟨23,by norm_num [Data.count]⟩:ℝ))
    (by norm_num [Data.radius]) ?_ ?_ ?_ ?_ hz
  all_goals norm_num [Data.centre,Data.coordinate,Data.radius,CertifiedTaylorModel.value]

theorem cell45 : ∀ z ∈ rectangle ((1/2)) (1) ((1551/160)) ((423/40)),
    ∃ i:Fin Data.count, ‖z-Data.centre i‖≤(Data.radius i:ℝ) :=
  split_y cell46 cell47

theorem cell41 : ∀ z ∈ rectangle ((1/2)) (1) ((141/16)) ((423/40)),
    ∃ i:Fin Data.count, ‖z-Data.centre i‖≤(Data.radius i:ℝ) :=
  split_y cell42 cell45

theorem cell33 : ∀ z ∈ rectangle ((1/2)) (1) ((141/20)) ((423/40)),
    ∃ i:Fin Data.count, ‖z-Data.centre i‖≤(Data.radius i:ℝ) :=
  split_y cell34 cell41

theorem cell51 : ∀ z ∈ rectangle ((1/2)) (1) ((423/40)) ((705/64)),
    ∃ i:Fin Data.count, ‖z-Data.centre i‖≤(Data.radius i:ℝ) := by
  intro z hz
  refine ⟨⟨24,by norm_num [Data.count]⟩,?_⟩
  apply rectangle_ball (c:=Data.centre ⟨24,by norm_num [Data.count]⟩) (r:=(Data.radius ⟨24,by norm_num [Data.count]⟩:ℝ))
    (by norm_num [Data.radius]) ?_ ?_ ?_ ?_ hz
  all_goals norm_num [Data.centre,Data.coordinate,Data.radius,CertifiedTaylorModel.value]

theorem cell53 : ∀ z ∈ rectangle ((1/2)) ((3/4)) ((705/64)) ((1833/160)),
    ∃ i:Fin Data.count, ‖z-Data.centre i‖≤(Data.radius i:ℝ) := by
  intro z hz
  refine ⟨⟨25,by norm_num [Data.count]⟩,?_⟩
  apply rectangle_ball (c:=Data.centre ⟨25,by norm_num [Data.count]⟩) (r:=(Data.radius ⟨25,by norm_num [Data.count]⟩:ℝ))
    (by norm_num [Data.radius]) ?_ ?_ ?_ ?_ hz
  all_goals norm_num [Data.centre,Data.coordinate,Data.radius,CertifiedTaylorModel.value]

theorem cell54 : ∀ z ∈ rectangle ((3/4)) (1) ((705/64)) ((1833/160)),
    ∃ i:Fin Data.count, ‖z-Data.centre i‖≤(Data.radius i:ℝ) := by
  intro z hz
  refine ⟨⟨26,by norm_num [Data.count]⟩,?_⟩
  apply rectangle_ball (c:=Data.centre ⟨26,by norm_num [Data.count]⟩) (r:=(Data.radius ⟨26,by norm_num [Data.count]⟩:ℝ))
    (by norm_num [Data.radius]) ?_ ?_ ?_ ?_ hz
  all_goals norm_num [Data.centre,Data.coordinate,Data.radius,CertifiedTaylorModel.value]

theorem cell52 : ∀ z ∈ rectangle ((1/2)) (1) ((705/64)) ((1833/160)),
    ∃ i:Fin Data.count, ‖z-Data.centre i‖≤(Data.radius i:ℝ) :=
  split_x cell53 cell54

theorem cell50 : ∀ z ∈ rectangle ((1/2)) (1) ((423/40)) ((1833/160)),
    ∃ i:Fin Data.count, ‖z-Data.centre i‖≤(Data.radius i:ℝ) :=
  split_y cell51 cell52

theorem cell57 : ∀ z ∈ rectangle ((1/2)) ((3/4)) ((1833/160)) ((3807/320)),
    ∃ i:Fin Data.count, ‖z-Data.centre i‖≤(Data.radius i:ℝ) := by
  intro z hz
  refine ⟨⟨27,by norm_num [Data.count]⟩,?_⟩
  apply rectangle_ball (c:=Data.centre ⟨27,by norm_num [Data.count]⟩) (r:=(Data.radius ⟨27,by norm_num [Data.count]⟩:ℝ))
    (by norm_num [Data.radius]) ?_ ?_ ?_ ?_ hz
  all_goals norm_num [Data.centre,Data.coordinate,Data.radius,CertifiedTaylorModel.value]

theorem cell58 : ∀ z ∈ rectangle ((3/4)) (1) ((1833/160)) ((3807/320)),
    ∃ i:Fin Data.count, ‖z-Data.centre i‖≤(Data.radius i:ℝ) := by
  intro z hz
  refine ⟨⟨28,by norm_num [Data.count]⟩,?_⟩
  apply rectangle_ball (c:=Data.centre ⟨28,by norm_num [Data.count]⟩) (r:=(Data.radius ⟨28,by norm_num [Data.count]⟩:ℝ))
    (by norm_num [Data.radius]) ?_ ?_ ?_ ?_ hz
  all_goals norm_num [Data.centre,Data.coordinate,Data.radius,CertifiedTaylorModel.value]

theorem cell56 : ∀ z ∈ rectangle ((1/2)) (1) ((1833/160)) ((3807/320)),
    ∃ i:Fin Data.count, ‖z-Data.centre i‖≤(Data.radius i:ℝ) :=
  split_x cell57 cell58

theorem cell60 : ∀ z ∈ rectangle ((1/2)) ((3/4)) ((3807/320)) ((987/80)),
    ∃ i:Fin Data.count, ‖z-Data.centre i‖≤(Data.radius i:ℝ) := by
  intro z hz
  refine ⟨⟨29,by norm_num [Data.count]⟩,?_⟩
  apply rectangle_ball (c:=Data.centre ⟨29,by norm_num [Data.count]⟩) (r:=(Data.radius ⟨29,by norm_num [Data.count]⟩:ℝ))
    (by norm_num [Data.radius]) ?_ ?_ ?_ ?_ hz
  all_goals norm_num [Data.centre,Data.coordinate,Data.radius,CertifiedTaylorModel.value]

theorem cell61 : ∀ z ∈ rectangle ((3/4)) (1) ((3807/320)) ((987/80)),
    ∃ i:Fin Data.count, ‖z-Data.centre i‖≤(Data.radius i:ℝ) := by
  intro z hz
  refine ⟨⟨30,by norm_num [Data.count]⟩,?_⟩
  apply rectangle_ball (c:=Data.centre ⟨30,by norm_num [Data.count]⟩) (r:=(Data.radius ⟨30,by norm_num [Data.count]⟩:ℝ))
    (by norm_num [Data.radius]) ?_ ?_ ?_ ?_ hz
  all_goals norm_num [Data.centre,Data.coordinate,Data.radius,CertifiedTaylorModel.value]

theorem cell59 : ∀ z ∈ rectangle ((1/2)) (1) ((3807/320)) ((987/80)),
    ∃ i:Fin Data.count, ‖z-Data.centre i‖≤(Data.radius i:ℝ) :=
  split_x cell60 cell61

theorem cell55 : ∀ z ∈ rectangle ((1/2)) (1) ((1833/160)) ((987/80)),
    ∃ i:Fin Data.count, ‖z-Data.centre i‖≤(Data.radius i:ℝ) :=
  split_y cell56 cell59

theorem cell49 : ∀ z ∈ rectangle ((1/2)) (1) ((423/40)) ((987/80)),
    ∃ i:Fin Data.count, ‖z-Data.centre i‖≤(Data.radius i:ℝ) :=
  split_y cell50 cell55

theorem cell65 : ∀ z ∈ rectangle ((1/2)) ((3/4)) ((987/80)) ((4089/320)),
    ∃ i:Fin Data.count, ‖z-Data.centre i‖≤(Data.radius i:ℝ) := by
  intro z hz
  refine ⟨⟨31,by norm_num [Data.count]⟩,?_⟩
  apply rectangle_ball (c:=Data.centre ⟨31,by norm_num [Data.count]⟩) (r:=(Data.radius ⟨31,by norm_num [Data.count]⟩:ℝ))
    (by norm_num [Data.radius]) ?_ ?_ ?_ ?_ hz
  all_goals norm_num [Data.centre,Data.coordinate,Data.radius,CertifiedTaylorModel.value]

theorem cell66 : ∀ z ∈ rectangle ((3/4)) (1) ((987/80)) ((4089/320)),
    ∃ i:Fin Data.count, ‖z-Data.centre i‖≤(Data.radius i:ℝ) := by
  intro z hz
  refine ⟨⟨32,by norm_num [Data.count]⟩,?_⟩
  apply rectangle_ball (c:=Data.centre ⟨32,by norm_num [Data.count]⟩) (r:=(Data.radius ⟨32,by norm_num [Data.count]⟩:ℝ))
    (by norm_num [Data.radius]) ?_ ?_ ?_ ?_ hz
  all_goals norm_num [Data.centre,Data.coordinate,Data.radius,CertifiedTaylorModel.value]

theorem cell64 : ∀ z ∈ rectangle ((1/2)) (1) ((987/80)) ((4089/320)),
    ∃ i:Fin Data.count, ‖z-Data.centre i‖≤(Data.radius i:ℝ) :=
  split_x cell65 cell66

theorem cell68 : ∀ z ∈ rectangle ((1/2)) ((3/4)) ((4089/320)) ((423/32)),
    ∃ i:Fin Data.count, ‖z-Data.centre i‖≤(Data.radius i:ℝ) := by
  intro z hz
  refine ⟨⟨33,by norm_num [Data.count]⟩,?_⟩
  apply rectangle_ball (c:=Data.centre ⟨33,by norm_num [Data.count]⟩) (r:=(Data.radius ⟨33,by norm_num [Data.count]⟩:ℝ))
    (by norm_num [Data.radius]) ?_ ?_ ?_ ?_ hz
  all_goals norm_num [Data.centre,Data.coordinate,Data.radius,CertifiedTaylorModel.value]

theorem cell69 : ∀ z ∈ rectangle ((3/4)) (1) ((4089/320)) ((423/32)),
    ∃ i:Fin Data.count, ‖z-Data.centre i‖≤(Data.radius i:ℝ) := by
  intro z hz
  refine ⟨⟨34,by norm_num [Data.count]⟩,?_⟩
  apply rectangle_ball (c:=Data.centre ⟨34,by norm_num [Data.count]⟩) (r:=(Data.radius ⟨34,by norm_num [Data.count]⟩:ℝ))
    (by norm_num [Data.radius]) ?_ ?_ ?_ ?_ hz
  all_goals norm_num [Data.centre,Data.coordinate,Data.radius,CertifiedTaylorModel.value]

theorem cell67 : ∀ z ∈ rectangle ((1/2)) (1) ((4089/320)) ((423/32)),
    ∃ i:Fin Data.count, ‖z-Data.centre i‖≤(Data.radius i:ℝ) :=
  split_x cell68 cell69

theorem cell63 : ∀ z ∈ rectangle ((1/2)) (1) ((987/80)) ((423/32)),
    ∃ i:Fin Data.count, ‖z-Data.centre i‖≤(Data.radius i:ℝ) :=
  split_y cell64 cell67

theorem cell72 : ∀ z ∈ rectangle ((1/2)) ((3/4)) ((423/32)) ((4371/320)),
    ∃ i:Fin Data.count, ‖z-Data.centre i‖≤(Data.radius i:ℝ) := by
  intro z hz
  refine ⟨⟨35,by norm_num [Data.count]⟩,?_⟩
  apply rectangle_ball (c:=Data.centre ⟨35,by norm_num [Data.count]⟩) (r:=(Data.radius ⟨35,by norm_num [Data.count]⟩:ℝ))
    (by norm_num [Data.radius]) ?_ ?_ ?_ ?_ hz
  all_goals norm_num [Data.centre,Data.coordinate,Data.radius,CertifiedTaylorModel.value]

theorem cell73 : ∀ z ∈ rectangle ((3/4)) (1) ((423/32)) ((4371/320)),
    ∃ i:Fin Data.count, ‖z-Data.centre i‖≤(Data.radius i:ℝ) := by
  intro z hz
  refine ⟨⟨36,by norm_num [Data.count]⟩,?_⟩
  apply rectangle_ball (c:=Data.centre ⟨36,by norm_num [Data.count]⟩) (r:=(Data.radius ⟨36,by norm_num [Data.count]⟩:ℝ))
    (by norm_num [Data.radius]) ?_ ?_ ?_ ?_ hz
  all_goals norm_num [Data.centre,Data.coordinate,Data.radius,CertifiedTaylorModel.value]

theorem cell71 : ∀ z ∈ rectangle ((1/2)) (1) ((423/32)) ((4371/320)),
    ∃ i:Fin Data.count, ‖z-Data.centre i‖≤(Data.radius i:ℝ) :=
  split_x cell72 cell73

theorem cell76 : ∀ z ∈ rectangle ((1/2)) ((3/4)) ((4371/320)) ((8883/640)),
    ∃ i:Fin Data.count, ‖z-Data.centre i‖≤(Data.radius i:ℝ) := by
  intro z hz
  refine ⟨⟨37,by norm_num [Data.count]⟩,?_⟩
  apply rectangle_ball (c:=Data.centre ⟨37,by norm_num [Data.count]⟩) (r:=(Data.radius ⟨37,by norm_num [Data.count]⟩:ℝ))
    (by norm_num [Data.radius]) ?_ ?_ ?_ ?_ hz
  all_goals norm_num [Data.centre,Data.coordinate,Data.radius,CertifiedTaylorModel.value]

theorem cell79 : ∀ z ∈ rectangle ((1/2)) ((5/8)) ((8883/640)) ((17907/1280)),
    ∃ i:Fin Data.count, ‖z-Data.centre i‖≤(Data.radius i:ℝ) := by
  intro z hz
  refine ⟨⟨38,by norm_num [Data.count]⟩,?_⟩
  apply rectangle_ball (c:=Data.centre ⟨38,by norm_num [Data.count]⟩) (r:=(Data.radius ⟨38,by norm_num [Data.count]⟩:ℝ))
    (by norm_num [Data.radius]) ?_ ?_ ?_ ?_ hz
  all_goals norm_num [Data.centre,Data.coordinate,Data.radius,CertifiedTaylorModel.value]

theorem cell81 : ∀ z ∈ rectangle ((1/2)) ((9/16)) ((17907/1280)) ((141/10)),
    ∃ i:Fin Data.count, ‖z-Data.centre i‖≤(Data.radius i:ℝ) := by
  intro z hz
  refine ⟨⟨39,by norm_num [Data.count]⟩,?_⟩
  apply rectangle_ball (c:=Data.centre ⟨39,by norm_num [Data.count]⟩) (r:=(Data.radius ⟨39,by norm_num [Data.count]⟩:ℝ))
    (by norm_num [Data.radius]) ?_ ?_ ?_ ?_ hz
  all_goals norm_num [Data.centre,Data.coordinate,Data.radius,CertifiedTaylorModel.value]

theorem cell82 : ∀ z ∈ rectangle ((9/16)) ((5/8)) ((17907/1280)) ((141/10)),
    ∃ i:Fin Data.count, ‖z-Data.centre i‖≤(Data.radius i:ℝ) := by
  intro z hz
  refine ⟨⟨40,by norm_num [Data.count]⟩,?_⟩
  apply rectangle_ball (c:=Data.centre ⟨40,by norm_num [Data.count]⟩) (r:=(Data.radius ⟨40,by norm_num [Data.count]⟩:ℝ))
    (by norm_num [Data.radius]) ?_ ?_ ?_ ?_ hz
  all_goals norm_num [Data.centre,Data.coordinate,Data.radius,CertifiedTaylorModel.value]

theorem cell80 : ∀ z ∈ rectangle ((1/2)) ((5/8)) ((17907/1280)) ((141/10)),
    ∃ i:Fin Data.count, ‖z-Data.centre i‖≤(Data.radius i:ℝ) :=
  split_x cell81 cell82

theorem cell78 : ∀ z ∈ rectangle ((1/2)) ((5/8)) ((8883/640)) ((141/10)),
    ∃ i:Fin Data.count, ‖z-Data.centre i‖≤(Data.radius i:ℝ) :=
  split_y cell79 cell80

theorem cell83 : ∀ z ∈ rectangle ((5/8)) ((3/4)) ((8883/640)) ((141/10)),
    ∃ i:Fin Data.count, ‖z-Data.centre i‖≤(Data.radius i:ℝ) := by
  intro z hz
  refine ⟨⟨41,by norm_num [Data.count]⟩,?_⟩
  apply rectangle_ball (c:=Data.centre ⟨41,by norm_num [Data.count]⟩) (r:=(Data.radius ⟨41,by norm_num [Data.count]⟩:ℝ))
    (by norm_num [Data.radius]) ?_ ?_ ?_ ?_ hz
  all_goals norm_num [Data.centre,Data.coordinate,Data.radius,CertifiedTaylorModel.value]

theorem cell77 : ∀ z ∈ rectangle ((1/2)) ((3/4)) ((8883/640)) ((141/10)),
    ∃ i:Fin Data.count, ‖z-Data.centre i‖≤(Data.radius i:ℝ) :=
  split_x cell78 cell83

theorem cell75 : ∀ z ∈ rectangle ((1/2)) ((3/4)) ((4371/320)) ((141/10)),
    ∃ i:Fin Data.count, ‖z-Data.centre i‖≤(Data.radius i:ℝ) :=
  split_y cell76 cell77

theorem cell85 : ∀ z ∈ rectangle ((3/4)) (1) ((4371/320)) ((8883/640)),
    ∃ i:Fin Data.count, ‖z-Data.centre i‖≤(Data.radius i:ℝ) := by
  intro z hz
  refine ⟨⟨42,by norm_num [Data.count]⟩,?_⟩
  apply rectangle_ball (c:=Data.centre ⟨42,by norm_num [Data.count]⟩) (r:=(Data.radius ⟨42,by norm_num [Data.count]⟩:ℝ))
    (by norm_num [Data.radius]) ?_ ?_ ?_ ?_ hz
  all_goals norm_num [Data.centre,Data.coordinate,Data.radius,CertifiedTaylorModel.value]

theorem cell86 : ∀ z ∈ rectangle ((3/4)) (1) ((8883/640)) ((141/10)),
    ∃ i:Fin Data.count, ‖z-Data.centre i‖≤(Data.radius i:ℝ) := by
  intro z hz
  refine ⟨⟨43,by norm_num [Data.count]⟩,?_⟩
  apply rectangle_ball (c:=Data.centre ⟨43,by norm_num [Data.count]⟩) (r:=(Data.radius ⟨43,by norm_num [Data.count]⟩:ℝ))
    (by norm_num [Data.radius]) ?_ ?_ ?_ ?_ hz
  all_goals norm_num [Data.centre,Data.coordinate,Data.radius,CertifiedTaylorModel.value]

theorem cell84 : ∀ z ∈ rectangle ((3/4)) (1) ((4371/320)) ((141/10)),
    ∃ i:Fin Data.count, ‖z-Data.centre i‖≤(Data.radius i:ℝ) :=
  split_y cell85 cell86

theorem cell74 : ∀ z ∈ rectangle ((1/2)) (1) ((4371/320)) ((141/10)),
    ∃ i:Fin Data.count, ‖z-Data.centre i‖≤(Data.radius i:ℝ) :=
  split_x cell75 cell84

theorem cell70 : ∀ z ∈ rectangle ((1/2)) (1) ((423/32)) ((141/10)),
    ∃ i:Fin Data.count, ‖z-Data.centre i‖≤(Data.radius i:ℝ) :=
  split_y cell71 cell74

theorem cell62 : ∀ z ∈ rectangle ((1/2)) (1) ((987/80)) ((141/10)),
    ∃ i:Fin Data.count, ‖z-Data.centre i‖≤(Data.radius i:ℝ) :=
  split_y cell63 cell70

theorem cell48 : ∀ z ∈ rectangle ((1/2)) (1) ((423/40)) ((141/10)),
    ∃ i:Fin Data.count, ‖z-Data.centre i‖≤(Data.radius i:ℝ) :=
  split_y cell49 cell62

theorem cell32 : ∀ z ∈ rectangle ((1/2)) (1) ((141/20)) ((141/10)),
    ∃ i:Fin Data.count, ‖z-Data.centre i‖≤(Data.radius i:ℝ) :=
  split_y cell33 cell48

theorem cell0 : ∀ z ∈ rectangle ((1/2)) (1) (0) ((141/10)),
    ∃ i:Fin Data.count, ‖z-Data.centre i‖≤(Data.radius i:ℝ) :=
  split_y cell1 cell32

theorem quarter_covered : ∀ z ∈ XiAdaptiveTiles.quarter (141/10),
    ∃ i:Fin Data.count, ‖z-Data.centre i‖≤(Data.radius i:ℝ) := cell0
end Reinmann.XiRectangle.Cover
