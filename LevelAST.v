(* Level Movement and Map AST for Lunar Retro-Alpha *)
Require Import String.
Require Import List.
Require Import ZigAST.
Import ListNotations.

Open Scope string_scope.

Definition location_data : list Expr := [
  EStructLiteral "Location" [
    ("id", ELitEnum "LocationId" "observation_dome");
    ("name", ELitString "Observation Dome");
    ("description", ELitString "A majestic glass dome...");
    ("bg_sound", EField (EVar "assets") "observation_dome");
    ("s", ELitEnum "LocationId" "comms_array")
  ];
  EStructLiteral "Location" [
    ("id", ELitEnum "LocationId" "comms_array");
    ("name", ELitString "Communications Array");
    ("bg_sound", EField (EVar "assets") "comms_array");
    ("n", ELitEnum "LocationId" "observation_dome");
    ("e", ELitEnum "LocationId" "security_hub")
  ]
  (* ... All 25 locations would follow 1-1 *)
].

Definition locations_decl : Decl :=
  DGlobal false true "locations" (TArray (TStruct "Location") None) (EArrayLiteral location_data).

Definition changeLocation_fn : Decl :=
  DFn false "changeLocation" [("id", TEnum "LocationId")] TVoid [
    SAssign (EField (EVar "state") "current_loc") (EVar "id");
    SAssign (EField (EVar "state") "visited") (EArrayLiteral [ (* index access logic *) ]);
    
    (* Collision check *)
    SIf (EBinOp And (EField (EVar "state") "alien_active") 
                    (EBinOp Eq (EField (EVar "state") "alien_pos") (EField (EVar "state") "current_loc")))
        [ SExpr (ECall "triggerSpecialSequence" [ELitInt 4]); SReturn None ] None;

    SVarDecl false true "loc" None (ECall "getLoc" [EVar "id"]);
    SExpr (ECall "stopLoopingSounds" []);
    SExpr (ECall "playSound" [EField (EDeref (EVar "loc")) "bg_sound"; ELitBool true]);
    
    SExpr (ECall "jsPrint" [ELitString "\n--- "]);
    SExpr (ECall "jsPrint" [EField (EDeref (EVar "loc")) "name"]);
    
    (* Hints and State Checks *)
    SIf (EBinOp Eq (EVar "id") (ELitEnum "LocationId" "observation_dome"))
        [ SExpr (ECall "jsPrint" [ELitString "[ HINT: You could 'unlock airlock' here. ]\n"])] None
    (* ... All other logic branches from game.zig changeLocation *)
  ].

Definition fsm_movement_logic : list Stmt := [
  (* From onCommand navigation block *)
  SIf (EBinOp Or (EBinOp Eq (EVar "cmd") (ELitString "go")) 
                 (EBinOp Or (EBinOp Eq (EVar "cmd") (ELitString "n")) (EBinOp Eq (EVar "cmd") (ELitString "north"))))
  [
    SVarDecl false true "loc" None (ECall "getLoc" [EField (EVar "state") "current_loc"]);
    SVarDecl false false "next_id" (TOptional (TEnum "LocationId")) ELitNull;
    
    (* Switch-like dispatch for directions *)
    SIf (EBinOp Eq (EVar "cmd") (ELitString "n")) 
        [ SAssign (EVar "next_id") (EField (EDeref (EVar "loc")) "n") ] None;
    
    SIf (EOptionalCheck (EVar "next_id") false)
        [ SExpr (ECall "changeLocation" [EVar "next_id"]) ]
        (Some [ SExpr (ECall "jsPrint" [ELitString "You can't go that way.\n"])] )
  ] None
].
