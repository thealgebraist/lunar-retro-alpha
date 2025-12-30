(* Game representation in Zig AST *)
Require Import String.
Require Import List.
Require Import ZigAST.
Import ListNotations.

Open Scope string_scope.

Definition game_program : Program :=
[
  (* --- JS Imports --- *)
  DExternFn "printText" [("ptr", TPtr (TInt 8 false) true); ("len", TUsize)] TVoid;
  DExternFn "playSound" [("ptr", TPtr (TInt 8 false) true); ("len", TUsize); ("loop", TBool)] TVoid;

  (* --- Enums --- *)
  DEnum "LocationId" [
    "observation_dome"; "comms_array"; "security_hub"; "elevator_lobby_alpha";
    "mess_hall"; "sleeping_pods"; "medical_lab"; "elevator_lobby_beta";
    "main_reactor"; "fuel_storage"; "battery_bank"; "maintenance_tunnels";
    "cargo_loading"; "oxygen_scrubbers"; "launch_control"; "escape_pod";
    "elevator_interior"
  ];

  DEnum "Item" ["control_board"; "battery"];

  (* --- Structs --- *)
  DStruct "GameState" [
    ("current_loc", TEnum "LocationId");
    ("inventory", TArray TBool (Some 2));
    ("pod_interface_ready", TBool);
    ("batteries_inserted", TInt 4 false)
  ];

  (* --- Globals --- *)
  DGlobal false false "state" (TStruct "GameState") 
    (EStructLiteral "GameState" [
      ("current_loc", EEnumLiteral "LocationId" "observation_dome");
      ("pod_interface_ready", ELitBool false)
    ]);

  (* --- Functions --- *)
  DFn true "init" [("seed", TInt 32 false)] TVoid [
    SAssign (EVar "rng_state") (EVar "seed");
    SExpr (ECall "changeLocation" [EEnumLiteral "LocationId" "observation_dome"])
  ];

  DFn true "tickWithSeed" [("dt", TFloat 32); ("seed", TInt 32 false)] TVoid [
    SIf (EField (EVar "state") "game_over") [SReturn None] None;
    SAssign (EVar "rng_state") (EBinOp Add (EVar "rng_state") (EVar "seed"));
    
    (* Announcement Logic Simplified *)
    SAssign (EField (EVar "state") "announcement_timer") 
            (EBinOp Add (EField (EVar "state") "announcement_timer") (EVar "dt"));
    SIf (EBinOp Ge (EField (EVar "state") "announcement_timer") (ELitInt 90)) [
      SAssign (EField (EVar "state") "announcement_timer") (ELitInt 0);
      SIf (EBinOp Le (ECast (TInt 8 false) (EField (EVar "state") "current_loc")) (ELitInt 15)) [
        SExpr (ECall "playSound" [EVar "evacuate_announcement_ptr"; EVar "evacuate_announcement_len"; ELitBool false])
      ] None
    ] None
  ]
].
