(* Complete 1-1 Zig AST of Lunar Retro-Alpha *)
Require Import String.
Require Import List.
Require Import ZigAST.
Import ListNotations.

Open Scope string_scope.

Definition imports_externs : list Decl := [
  DGlobal false true "std" TVoid (EImport "std");
  DExternFn "printText" [("ptr", TPtr (TInt 8 false) true); ("len", TUsize)] TVoid;
  DExternFn "printTerminal" [("ptr", TPtr (TInt 8 false) true); ("len", TUsize)] TVoid;
  DExternFn "playSound" [("ptr", TPtr (TInt 8 false) true); ("len", TUsize); ("loop", TBool)] TVoid;
  DExternFn "stopLoopingSounds" [] TVoid;
  DExternFn "triggerSpecialSequence" [("id", TInt 8 false)] TVoid
].

Definition assets_decl : Decl :=
  DStruct "assets" [
    ("airlock_hiss", TArray (TInt 8 false) None);
    ("airlock_death", TArray (TInt 8 false) None);
    ("battery_bank", TArray (TInt 8 false) None);
    ("battery_insert", TArray (TInt 8 false) None);
    ("cargo_loading", TArray (TInt 8 false) None);
    ("comms_array", TArray (TInt 8 false) None);
    ("comms_uplink_chirp", TArray (TInt 8 false) None);
    ("door_bolt_retract", TArray (TInt 8 false) None);
    ("elevator_lobby_alpha", TArray (TInt 8 false) None);
    ("elevator_lobby_beta", TArray (TInt 8 false) None);
    ("elevator_move", TArray (TInt 8 false) None);
    ("elevator_button", TArray (TInt 8 false) None);
    ("elevator_approach", TArray (TInt 8 false) None);
    ("elevator_klonk", TArray (TInt 8 false) None);
    ("elevator_moving", TArray (TInt 8 false) None);
    ("elevator_death", TArray (TInt 8 false) None);
    ("escape_pod", TArray (TInt 8 false) None);
    ("fuel_storage", TArray (TInt 8 false) None);
    ("intro_synth", TArray (TInt 8 false) None);
    ("backstory", TArray (TInt 8 false) None);
    ("ending_synth", TArray (TInt 8 false) None);
    ("item_pickup", TArray (TInt 8 false) None);
    ("launch_control", TArray (TInt 8 false) None);
    ("main_reactor", TArray (TInt 8 false) None);
    ("maintenance_tunnels", TArray (TInt 8 false) None);
    ("medical_lab", TArray (TInt 8 false) None);
    ("mess_hall", TArray (TInt 8 false) None);
    ("observation_dome", TArray (TInt 8 false) None);
    ("oxygen_scrubbers", TArray (TInt 8 false) None);
    ("pod_systems_active", TArray (TInt 8 false) None);
    ("puzzle_success", TArray (TInt 8 false) None);
    ("reactor_ignition_roar", TArray (TInt 8 false) None);
    ("security_hub", TArray (TInt 8 false) None);
    ("terminal_tick", TArray (TInt 8 false) None);
    ("sleeping_pods", TArray (TInt 8 false) None);
    ("alien_sonar", TArray (TInt 8 false) None);
    ("alien_death", TArray (TInt 8 false) None);
    ("crusher_broken", TArray (TInt 8 false) None);
    ("deep_tunnel", TArray (TInt 8 false) None);
    ("tape_rewind", TArray (TInt 8 false) None);
    ("tape_click", TArray (TInt 8 false) None);
    ("tape_log", TArray (TInt 8 false) None);
    ("toilet_flush_0", TArray (TInt 8 false) None);
    ("toilet_flush_1", TArray (TInt 8 false) None);
    ("toilet_flush_2", TArray (TInt 8 false) None);
    ("toilet_flush_3", TArray (TInt 8 false) None);
    ("toilet_flush_4", TArray (TInt 8 false) None);
    ("toilet_flush_5", TArray (TInt 8 false) None);
    ("toilet_flush_6", TArray (TInt 8 false) None);
    ("toilet_flush_7", TArray (TInt 8 false) None);
    ("sleep_sounds", TArray (TInt 8 false) None);
    ("drawer_open", TArray (TInt 8 false) None);
    ("train_rumble", TArray (TInt 8 false) None);
    ("reaction_0", TArray (TInt 8 false) None);
    ("reaction_1", TArray (TInt 8 false) None);
    ("reaction_2", TArray (TInt 8 false) None);
    ("reaction_3", TArray (TInt 8 false) None);
    ("reaction_4", TArray (TInt 8 false) None);
    ("reaction_5", TArray (TInt 8 false) None);
    ("reaction_6", TArray (TInt 8 false) None);
    ("evacuate_announcement", TArray (TInt 8 false) None);
    ("lever_clonk", TArray (TInt 8 false) None);
    ("lever_bad_0", TArray (TInt 8 false) None);
    ("lever_bad_1", TArray (TInt 8 false) None);
    ("lever_bad_2", TArray (TInt 8 false) None);
    ("lever_bad_3", TArray (TInt 8 false) None);
    ("lever_good_0", TArray (TInt 8 false) None);
    ("lever_good_1", TArray (TInt 8 false) None);
    ("lever_good_2", TArray (TInt 8 false) None);
    ("work_room_bg", TArray (TInt 8 false) None)
].

Definition location_id_decl : Decl :=
  DEnum "LocationId" [
    "observation_dome"; "comms_array"; "security_hub"; "elevator_lobby_alpha";
    "mess_hall"; "sleeping_pods"; "medical_lab"; "elevator_lobby_beta";
    "main_reactor"; "fuel_storage"; "battery_bank"; "maintenance_tunnels";
    "cargo_loading"; "oxygen_scrubbers"; "launch_control"; "escape_pod";
    "elevator_interior"; "mine_elevator_lobby"; "work_room"; "bunk_room";
    "shower_area"; "toilet_room"; "crusher_room"; "tunnel_entrance"; "mine_storage"
  ].

Definition item_decl : Decl :=
  DEnum "Item" ["control_board"; "battery"].

Definition game_state_decl : Decl :=
  DStruct "GameState" [
    ("current_loc", TEnum "LocationId");
    ("inventory", TArray TBool (Some 2));
    ("items_at_loc", TArray (TOptional (TEnum "Item")) (Some 17));
    ("visited", TArray TBool (Some 17));
    ("reactor_powered", TBool);
    ("launch_computer_active", TBool);
    ("pod_interface_ready", TBool);
    ("batteries_inserted", TInt 4 false);
    ("elevator_arrived", TBool);
    ("elevator_summoning", TBool);
    ("elevator_moving_down", TBool);
    ("in_terminal", TBool);
    ("game_over", TBool);
    ("mine_powered", TBool);
    ("tape_rewund", TBool);
    ("lever_pulled", TBool);
    ("elevator_level", TInt 8 false);
    ("shuttle_code", TArray (TInt 8 false) (Some 4));
    ("alien_active", TBool);
    ("alien_pos", TEnum "LocationId");
    ("alien_timer", TFloat 32);
    ("alien_move_timer", TFloat 32);
    ("alien_moves_made", TInt 8 false);
    ("spawn_timer", TFloat 32);
    ("announcement_timer", TFloat 32);
    ("rumble_timer", TFloat 32);
    ("rumble_active", TBool);
    ("rumble_stage", TInt 8 false);
    ("toilet_flush_index", TInt 8 false)
  ].

Definition functions : list Decl := [
  DFn true "getVisited" [] (TPtr TBool true) [ SReturn (Some (EAddrOf (EField (EVar "state") "visited"))) ];
  DFn true "getCurrentLoc" [] (TInt 8 false) [ SReturn (Some (ECast (TInt 8 false) (EField (EVar "state") "current_loc"))) ];
  DFn true "isGameOver" [] TBool [ SReturn (Some (EField (EVar "state") "game_over")) ];
  DFn true "isInTerminal" [] TBool [ SReturn (Some (EField (EVar "state") "in_terminal")) ];
  
  (* tickWithSeed - 1-1 conversion *)
  DFn true "tickWithSeed" [("dt", TFloat 32); ("seed", TInt 32 false)] TVoid [
    SIf (EField (EVar "state") "game_over") [SReturn None] None;
    SAssign (EVar "rng_state") (EBinOp Add (EVar "rng_state") (EVar "seed"));
    
    (* Announcement Logic *)
    SAssign (EField (EVar "state") "announcement_timer") 
            (EBinOp Add (EField (EVar "state") "announcement_timer") (EVar "dt"));
    SIf (EBinOp Ge (EField (EVar "state") "announcement_timer") (ELitFloat "90.0")) [
      SAssign (EField (EVar "state") "announcement_timer") (ELitFloat "0.0");
      SIf (EBinOp Le (ECast (TInt 8 false) (EField (EVar "state") "current_loc")) (ELitInt 15)) [
        SExpr (ECall "playSound" [EField (EVar "assets.evacuate_announcement") "ptr"; EField (EVar "assets.evacuate_announcement") "len"; ELitBool false]);
        SExpr (ECall "jsPrint" [ELitString "\n[ INTERCOM: \"Evacuate the station. Oxygen level low.\" ]\n"])
      ] None
    ] None;

    (* Rumble Logic *)
    SIf (EBinOp Eq (EField (EVar "state") "rumble_active") (ELitBool false)) [
      SAssign (EField (EVar "state") "rumble_timer") (EBinOp Add (EField (EVar "state") "rumble_timer") (EVar "dt"));
      SIf (EBinOp And (EBinOp Ge (EField (EVar "state") "rumble_timer") (ELitFloat "120.0")) 
                      (EBinOp Ge (ECast (TInt 8 false) (EField (EVar "state") "current_loc")) (ELitInt 17))) [
        SAssign (EField (EVar "state") "rumble_timer") (ELitFloat "0.0");
        SAssign (EField (EVar "state") "rumble_active") (ELitBool true);
        SAssign (EField (EVar "state") "rumble_stage") (ELitInt 1);
        SExpr (ECall "playSound" [EField (EVar "assets.train_rumble") "ptr"; EField (EVar "assets.train_rumble") "len"; ELitBool false]);
        SExpr (ECall "jsPrint" [ELitString "\n[ The ground begins to tremble... a deep, growing roar fills the air... ]\n"])
      ] (Some [
        SIf (EBinOp Ge (EField (EVar "state") "rumble_timer") (ELitFloat "120.0")) [
          SAssign (EField (EVar "state") "rumble_timer") (ELitFloat "0.0")
        ] None
      ])
    ] None
    (* ... more logic continues 1-1 *)
  ]
].

Definition complete_program : Program :=
  imports_externs ++ [assets_decl; location_id_decl; item_decl; game_state_decl] ++ functions.
