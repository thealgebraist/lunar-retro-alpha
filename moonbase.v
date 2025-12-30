(* Coq Formalization of Lunar Retro-Alpha *)
Require Import List.
Import ListNotations.

Inductive Location : Type :=
| ObservationDome
| CommsArray
| SecurityHub
| ElevatorLobbyAlpha
| MessHall
| SleepingPods
| MedicalLab
| ElevatorLobbyBeta
| MainReactor
| FuelStorage
| BatteryBank
| MaintenanceTunnels
| CargoLoading
| OxygenScrubbers
| LaunchControl
| EscapePod
| ElevatorInterior
| MineLobby
| WorkRoom
| BunkRoom
| ShowerArea
| ToiletRoom
| CrusherRoom
| TunnelEntrance
| MineStorage.

Inductive Item : Type :=
| ControlBoard
| HighCapacityBattery.

Definition Adjacent (l1 l2 : Location) : Prop :=
match l1, l2 with
| ObservationDome, CommsArray => True
| CommsArray, ObservationDome => True
| CommsArray, SecurityHub => True
| SecurityHub, CommsArray => True
| SecurityHub, ElevatorLobbyAlpha => True
| ElevatorLobbyAlpha, SecurityHub => True
| ElevatorLobbyAlpha, MessHall => True
| MessHall, ElevatorLobbyAlpha => True
| MessHall, SleepingPods => True
| SleepingPods, MessHall => True
| SleepingPods, MedicalLab => True
| MedicalLab, SleepingPods => True
| MedicalLab, ElevatorLobbyBeta => True
| ElevatorLobbyBeta, MedicalLab => True
| ElevatorLobbyBeta, MainReactor => True
| MainReactor, ElevatorLobbyBeta => True
| MainReactor, FuelStorage => True
| FuelStorage, MainReactor => True
| FuelStorage, BatteryBank => True
| BatteryBank, FuelStorage => True
| BatteryBank, MaintenanceTunnels => True
| MaintenanceTunnels, BatteryBank => True
| MaintenanceTunnels, CargoLoading => True
| CargoLoading, MaintenanceTunnels => True
| CargoLoading, OxygenScrubbers => True
| OxygenScrubbers, CargoLoading => True
| OxygenScrubbers, LaunchControl => True
| LaunchControl, OxygenScrubbers => True
| LaunchControl, EscapePod => True
| EscapePod, LaunchControl => True
| ElevatorLobbyAlpha, ElevatorInterior => True
| ElevatorInterior, ElevatorLobbyAlpha => True
| ElevatorLobbyBeta, ElevatorInterior => True
| ElevatorInterior, ElevatorLobbyBeta => True
| MineLobby, ElevatorInterior => True
| ElevatorInterior, MineLobby => True
| MineLobby, WorkRoom => True
| WorkRoom, MineLobby => True
| MineLobby, BunkRoom => True
| BunkRoom, MineLobby => True
| BunkRoom, ShowerArea => True
| ShowerArea, BunkRoom => True
| ShowerArea, ToiletRoom => True
| ToiletRoom, ShowerArea => True
| ToiletRoom, MineStorage => True
| MineStorage, ToiletRoom => True
| MineStorage, CrusherRoom => True
| CrusherRoom, MineStorage => True
| CrusherRoom, TunnelEntrance => True
| TunnelEntrance, CrusherRoom => True
| _, _ => False
end.

Record GameState : Type := {
  current_loc : Location;
  has_board : bool;
  has_battery : bool;
  board_at : option Location;
  battery_at : option Location;
  pod_ready : bool;
  battery_ready : bool;
}.

Definition InitialState : GameState := {|
  current_loc := ObservationDome;
  has_board := false;
  has_battery := false;
  board_at := Some CommsArray;
  battery_at := Some SleepingPods;
  pod_ready := false;
  battery_ready := false;
|}.

Definition WinCondition (s : GameState) : Prop :=
  s.(pod_ready) = true /\ s.(battery_ready) = true.

Inductive Action : Type :=
| Move (l : Location)
| Take (i : Item)
| Use (i : Item).

Inductive Step : GameState -> Action -> GameState -> Prop :=
| StepMove : forall s l,
    Adjacent s.(current_loc) l ->
    Step s (Move l) {|
      current_loc := l;
      has_board := s.(has_board);
      has_battery := s.(has_battery);
      board_at := s.(board_at);
      battery_at := s.(battery_at);
      pod_ready := s.(pod_ready);
      battery_ready := s.(battery_ready)
    |}
| StepTakeBoard : forall s,
    s.(current_loc) = CommsArray ->
    s.(board_at) = Some CommsArray ->
    Step s (Take ControlBoard) {|
      current_loc := s.(current_loc);
      has_board := true;
      has_battery := s.(has_battery);
      board_at := None;
      battery_at := s.(battery_at);
      pod_ready := s.(pod_ready);
      battery_ready := s.(battery_ready)
    |}
| StepTakeBattery : forall s,
    s.(current_loc) = SleepingPods ->
    s.(battery_at) = Some SleepingPods ->
    Step s (Take HighCapacityBattery) {|
      current_loc := s.(current_loc);
      has_board := s.(has_board);
      has_battery := true;
      board_at := s.(board_at);
      battery_at := None;
      pod_ready := s.(pod_ready);
      battery_ready := s.(battery_ready)
    |}
| StepUseBoard : forall s,
    s.(current_loc) = EscapePod ->
    s.(has_board) = true ->
    Step s (Use ControlBoard) {|
      current_loc := s.(current_loc);
      has_board := false;
      has_battery := s.(has_battery);
      board_at := s.(board_at);
      battery_at := s.(battery_at);
      pod_ready := true;
      battery_ready := s.(battery_ready)
    |}
| StepUseBattery : forall s,
    s.(current_loc) = EscapePod ->
    s.(has_battery) = true ->
    Step s (Use HighCapacityBattery) {|
      current_loc := s.(current_loc);
      has_board := s.(has_board);
      has_battery := false;
      board_at := s.(board_at);
      battery_at := s.(battery_at);
      pod_ready := s.(pod_ready);
      battery_ready := true
    |}.

Inductive Reachable : GameState -> GameState -> Prop :=
| ReachBase : forall s, Reachable s s
| ReachStep : forall s1 s2 s3 a,
    Reachable s1 s2 ->
    Step s2 a s3 ->
    Reachable s1 s3.

Theorem game_solvable : exists s, Reachable InitialState s /\ WinCondition s.
Proof.
  set (s0 := InitialState).
  assert (R1: Reachable s0 {| current_loc := CommsArray; has_board := false; has_battery := false; board_at := Some CommsArray; battery_at := Some SleepingPods; pod_ready := false; battery_ready := false |}) by (eapply ReachStep; [ apply ReachBase | apply StepMove; simpl; apply I ]).
  assert (R2: Reachable s0 {| current_loc := CommsArray; has_board := true; has_battery := false; board_at := None; battery_at := Some SleepingPods; pod_ready := false; battery_ready := false |}) by (eapply ReachStep; [ apply R1 | apply StepTakeBoard; reflexivity ]).
  assert (R3: Reachable s0 {| current_loc := SecurityHub; has_board := true; has_battery := false; board_at := None; battery_at := Some SleepingPods; pod_ready := false; battery_ready := false |}) by (eapply ReachStep; [ apply R2 | apply StepMove; simpl; apply I ]).
  assert (R4: Reachable s0 {| current_loc := ElevatorLobbyAlpha; has_board := true; has_battery := false; board_at := None; battery_at := Some SleepingPods; pod_ready := false; battery_ready := false |}) by (eapply ReachStep; [ apply R3 | apply StepMove; simpl; apply I ]).
  assert (R5: Reachable s0 {| current_loc := MessHall; has_board := true; has_battery := false; board_at := None; battery_at := Some SleepingPods; pod_ready := false; battery_ready := false |}) by (eapply ReachStep; [ apply R4 | apply StepMove; simpl; apply I ]).
  assert (R6: Reachable s0 {| current_loc := SleepingPods; has_board := true; has_battery := false; board_at := None; battery_at := Some SleepingPods; pod_ready := false; battery_ready := false |}) by (eapply ReachStep; [ apply R5 | apply StepMove; simpl; apply I ]).
  assert (R7: Reachable s0 {| current_loc := SleepingPods; has_board := true; has_battery := true; board_at := None; battery_at := None; pod_ready := false; battery_ready := false |}) by (eapply ReachStep; [ apply R6 | apply StepTakeBattery; reflexivity ]).
  assert (R8: Reachable s0 {| current_loc := MedicalLab; has_board := true; has_battery := true; board_at := None; battery_at := None; pod_ready := false; battery_ready := false |}) by (eapply ReachStep; [ apply R7 | apply StepMove; simpl; apply I ]).
  assert (R9: Reachable s0 {| current_loc := ElevatorLobbyBeta; has_board := true; has_battery := true; board_at := None; battery_at := None; pod_ready := false; battery_ready := false |}) by (eapply ReachStep; [ apply R8 | apply StepMove; simpl; apply I ]).
  assert (R10: Reachable s0 {| current_loc := MainReactor; has_board := true; has_battery := true; board_at := None; battery_at := None; pod_ready := false; battery_ready := false |}) by (eapply ReachStep; [ apply R9 | apply StepMove; simpl; apply I ]).
  assert (R11: Reachable s0 {| current_loc := FuelStorage; has_board := true; has_battery := true; board_at := None; battery_at := None; pod_ready := false; battery_ready := false |}) by (eapply ReachStep; [ apply R10 | apply StepMove; simpl; apply I ]).
  assert (R12: Reachable s0 {| current_loc := BatteryBank; has_board := true; has_battery := true; board_at := None; battery_at := None; pod_ready := false; battery_ready := false |}) by (eapply ReachStep; [ apply R11 | apply StepMove; simpl; apply I ]).
  assert (R13: Reachable s0 {| current_loc := MaintenanceTunnels; has_board := true; has_battery := true; board_at := None; battery_at := None; pod_ready := false; battery_ready := false |}) by (eapply ReachStep; [ apply R12 | apply StepMove; simpl; apply I ]).
  assert (R14: Reachable s0 {| current_loc := CargoLoading; has_board := true; has_battery := true; board_at := None; battery_at := None; pod_ready := false; battery_ready := false |}) by (eapply ReachStep; [ apply R13 | apply StepMove; simpl; auto ]).
  assert (R15: Reachable s0 {| current_loc := OxygenScrubbers; has_board := true; has_battery := true; board_at := None; battery_at := None; pod_ready := false; battery_ready := false |}) by (eapply ReachStep; [ apply R14 | apply StepMove; simpl; apply I ]).
  assert (R16: Reachable s0 {| current_loc := LaunchControl; has_board := true; has_battery := true; board_at := None; battery_at := None; pod_ready := false; battery_ready := false |}) by (eapply ReachStep; [ apply R15 | apply StepMove; simpl; apply I ]).
  assert (R17: Reachable s0 {| current_loc := EscapePod; has_board := true; has_battery := true; board_at := None; battery_at := None; pod_ready := false; battery_ready := false |}) by (eapply ReachStep; [ apply R16 | apply StepMove; simpl; apply I ]).
  assert (R18: Reachable s0 {| current_loc := EscapePod; has_board := false; has_battery := true; board_at := None; battery_at := None; pod_ready := true; battery_ready := false |}) by (eapply ReachStep; [ apply R17 | apply StepUseBoard; reflexivity ]).
  assert (R19: Reachable s0 {| current_loc := EscapePod; has_board := false; has_battery := false; board_at := None; battery_at := None; pod_ready := true; battery_ready := true |}) by (eapply ReachStep; [ apply R18 | apply StepUseBattery; reflexivity ]).
  exists {| current_loc := EscapePod; has_board := false; has_battery := false; board_at := None; battery_at := None; pod_ready := true; battery_ready := true |}; split; [ apply R19 | split; reflexivity ].
Qed.

Definition PodInvariant (s : GameState) : Prop :=
  if s.(pod_ready) then s.(has_board) = false else True.

Lemma invariant_holds : forall s, Reachable InitialState s -> PodInvariant s.
Proof.
  intros s H; induction H.
  - unfold PodInvariant, InitialState; simpl; auto.
  - unfold PodInvariant in *; destruct a; inversion H0; subst; simpl in *; auto;
    destruct (pod_ready s2) eqn:P; auto.
Qed.

Lemma mine_reachable : exists s, Reachable InitialState s /\ s.(current_loc) = MineLobby.
Proof.
  set (s0 := InitialState).
  assert (R : Reachable s0 {| current_loc := MineLobby; has_board := false; has_battery := false; board_at := Some CommsArray; battery_at := Some SleepingPods; pod_ready := false; battery_ready := false |}).
  { eapply ReachStep; [ | apply StepMove; simpl; apply I ].
    eapply ReachStep; [ | apply StepMove; simpl; apply I ].
    eapply ReachStep; [ | apply StepMove; simpl; apply I ].
    eapply ReachStep; [ | apply StepMove; simpl; apply I ].
    eapply ReachStep; [ | apply StepMove; simpl; apply I ].
    apply ReachBase. }
  exists {| current_loc := MineLobby; has_board := false; has_battery := false; board_at := Some CommsArray; battery_at := Some SleepingPods; pod_ready := false; battery_ready := false |}; split; [ apply R | reflexivity ].
Qed.