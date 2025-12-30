const std = @import("std");

// --- JS Imports ---
extern fn printText(ptr: [*]const u8, len: usize) void;
extern fn printTerminal(ptr: [*]const u8, len: usize) void;
extern fn playSound(ptr: [*]const u8, len: usize, loop: bool) void;
extern fn stopLoopingSounds() void;
extern fn triggerSpecialSequence(id: u8) void;

// --- Assets ---
const assets = struct {
    const airlock_hiss = @embedFile("moon_base_assets/airlock_hiss.ogg");
    const airlock_death = @embedFile("moon_base_assets/airlock_death.ogg");
    const battery_bank = @embedFile("moon_base_assets/battery_bank.ogg");
    const battery_insert = @embedFile("moon_base_assets/battery_insert.ogg");
    const cargo_loading = @embedFile("moon_base_assets/cargo_loading.ogg");
    const comms_array = @embedFile("moon_base_assets/comms_array.ogg");
    const comms_uplink_chirp = @embedFile("moon_base_assets/comms_uplink_chirp.ogg");
    const door_bolt_retract = @embedFile("moon_base_assets/door_bolt_retract.ogg");
    const elevator_lobby_alpha = @embedFile("moon_base_assets/elevator_lobby_alpha.ogg");
    const elevator_lobby_beta = @embedFile("moon_base_assets/elevator_lobby_beta.ogg");
    const elevator_move = @embedFile("moon_base_assets/elevator_move.ogg");
    const elevator_button = @embedFile("moon_base_assets/elevator_button.ogg");
    const elevator_approach = @embedFile("moon_base_assets/elevator_approach.ogg");
    const elevator_klonk = @embedFile("moon_base_assets/elevator_klonk.ogg");
    const elevator_moving = @embedFile("moon_base_assets/elevator_moving.ogg");
    const elevator_death = @embedFile("moon_base_assets/elevator_death.ogg");
    const escape_pod = @embedFile("moon_base_assets/escape_pod.ogg");
    const fuel_storage = @embedFile("moon_base_assets/fuel_storage.ogg");
    const intro_synth = @embedFile("moon_base_assets/intro_synth.ogg");
    const backstory = @embedFile("moon_base_assets/backstory.ogg");
    const ending_synth = @embedFile("moon_base_assets/ending_synth.ogg");
    const item_pickup = @embedFile("moon_base_assets/item_pickup.ogg");
    const launch_control = @embedFile("moon_base_assets/launch_control.ogg");
    const main_reactor = @embedFile("moon_base_assets/main_reactor.ogg");
    const maintenance_tunnels = @embedFile("moon_base_assets/maintenance_tunnels.ogg");
    const medical_lab = @embedFile("moon_base_assets/medical_lab.ogg");
    const mess_hall = @embedFile("moon_base_assets/mess_hall.ogg");
    const observation_dome = @embedFile("moon_base_assets/observation_dome.ogg");
    const oxygen_scrubbers = @embedFile("moon_base_assets/oxygen_scrubbers.ogg");
    const pod_systems_active = @embedFile("moon_base_assets/pod_systems_active.ogg");
    const puzzle_success = @embedFile("moon_base_assets/puzzle_success.ogg");
    const reactor_ignition_roar = @embedFile("moon_base_assets/reactor_ignition_roar.ogg");
    const security_hub = @embedFile("moon_base_assets/security_hub.ogg");
    const terminal_tick = @embedFile("moon_base_assets/terminal_tick.ogg");
    const sleeping_pods = @embedFile("moon_base_assets/sleeping_pods.ogg");
    const alien_sonar = @embedFile("moon_base_assets/alien_sonar.ogg");
    const alien_death = @embedFile("moon_base_assets/alien_death.ogg");
    
    // Mine Assets
    const crusher_broken = @embedFile("moon_base_assets/crusher_broken.ogg");
    const deep_tunnel = @embedFile("moon_base_assets/deep_tunnel.ogg");
    const tape_rewind = @embedFile("moon_base_assets/tape_rewind.ogg");
    const tape_click = @embedFile("moon_base_assets/tape_click.ogg");
    const tape_log = @embedFile("moon_base_assets/tape_log.ogg");
    const toilet_flush_0 = @embedFile("moon_base_assets/toilet_flush_0.ogg");
    const toilet_flush_1 = @embedFile("moon_base_assets/toilet_flush_1.ogg");
    const toilet_flush_2 = @embedFile("moon_base_assets/toilet_flush_2.ogg");
    const toilet_flush_3 = @embedFile("moon_base_assets/toilet_flush_3.ogg");
    const toilet_flush_4 = @embedFile("moon_base_assets/toilet_flush_4.ogg");
    const toilet_flush_5 = @embedFile("moon_base_assets/toilet_flush_5.ogg");
    const toilet_flush_6 = @embedFile("moon_base_assets/toilet_flush_6.ogg");
    const toilet_flush_7 = @embedFile("moon_base_assets/toilet_flush_7.ogg");
    const sleep_sounds = @embedFile("moon_base_assets/sleep_sounds.ogg");
    const drawer_open = @embedFile("moon_base_assets/drawer_open.ogg");
    const train_rumble = @embedFile("moon_base_assets/train_rumble.ogg");
    const reaction_0 = @embedFile("moon_base_assets/reaction_0.ogg");
    const reaction_1 = @embedFile("moon_base_assets/reaction_1.ogg");
    const reaction_2 = @embedFile("moon_base_assets/reaction_2.ogg");
    const reaction_3 = @embedFile("moon_base_assets/reaction_3.ogg");
    const reaction_4 = @embedFile("moon_base_assets/reaction_4.ogg");
    const reaction_5 = @embedFile("moon_base_assets/reaction_5.ogg");
    const reaction_6 = @embedFile("moon_base_assets/reaction_6.ogg");
    const evacuate_announcement = @embedFile("moon_base_assets/evacuate_announcement.ogg");

    const lever_clonk = @embedFile("moon_base_assets/lever_clonk.ogg");
    const lever_bad_0 = @embedFile("moon_base_assets/lever_bad_0.ogg");
    const lever_bad_1 = @embedFile("moon_base_assets/lever_bad_1.ogg");
    const lever_bad_2 = @embedFile("moon_base_assets/lever_bad_2.ogg");
    const lever_bad_3 = @embedFile("moon_base_assets/lever_bad_3.ogg");
    const lever_good_0 = @embedFile("moon_base_assets/lever_good_0.ogg");
    const lever_good_1 = @embedFile("moon_base_assets/lever_good_1.ogg");
    const lever_good_2 = @embedFile("moon_base_assets/lever_good_2.ogg");
    const work_room_bg = @embedFile("moon_base_assets/work_room_bg.ogg");
};

const LocationId = enum {
    observation_dome,
    comms_array,
    security_hub,
    elevator_lobby_alpha,
    mess_hall,
    sleeping_pods,
    medical_lab,
    elevator_lobby_beta,
    main_reactor,
    fuel_storage,
    battery_bank,
    maintenance_tunnels,
    cargo_loading,
    oxygen_scrubbers,
    launch_control,
    escape_pod,
    elevator_interior,
    // Mine Level
    mine_elevator_lobby,
    work_room,
    bunk_room,
    shower_area,
    toilet_room,
    crusher_room,
    tunnel_entrance,
    mine_storage,
};

const Item = enum {
    control_board,
    battery,

    fn name(self: Item) []const u8 {
        return switch (self) {
            .control_board => "Control Board (Launch System)",
            .battery => "High-Capacity Battery",
        };
    }
};

const Location = struct {
    id: LocationId,
    name: []const u8,
    description: []const u8,
    item_description: []const u8 = "You don't see anything special about the item.",
    bg_sound: []const u8,
    n: ?LocationId = null,
    s: ?LocationId = null,
    e: ?LocationId = null,
    w: ?LocationId = null,
    u: ?LocationId = null,
    d: ?LocationId = null,
};

const GameState = struct {
    current_loc: LocationId = .observation_dome,
    inventory: [2]bool = [_]bool{false} ** 2,
    items_at_loc: [17]?Item = [_]?Item{null} ** 17,
    visited: [17]bool = [_]bool{false} ** 17,
    reactor_powered: bool = true,
    launch_computer_active: bool = true,
    pod_interface_ready: bool = false,
    batteries_inserted: u4 = 0,
    elevator_arrived: bool = false,
    elevator_summoning: bool = false,
    elevator_moving_down: bool = false,
    in_terminal: bool = false,
    game_over: bool = false,
    
    // Mine State
    mine_powered: bool = false,
    tape_rewound: bool = false,
    lever_pulled: bool = false,
    elevator_level: u8 = 0, // 0: Top, 1: Bottom (Mine)
    shuttle_code: [4]u8 = [_]u8{0,0,0,0},

    // Alien State
    alien_active: bool = false,
    alien_pos: LocationId = .observation_dome,
    alien_timer: f32 = 0.0,
    alien_move_timer: f32 = 0.0,
    alien_moves_made: u8 = 0,
    spawn_timer: f32 = 0.0,
    announcement_timer: f32 = 0.0,
    rumble_timer: f32 = 0.0,
    rumble_active: bool = false,
    rumble_stage: u8 = 0, // 0: inactive, 1: playing rumble, 2: playing reaction

    fn hasItem(self: *GameState, item: Item) bool {
        return self.inventory[@intFromEnum(item)];
    }

    fn setItem(self: *GameState, item: Item, val: bool) void {
        self.inventory[@intFromEnum(item)] = val;
    }
};

var state = GameState{};

export fn getVisited() [*]const bool { return &state.visited; }
export fn getCurrentLoc() u8 { return @intFromEnum(state.current_loc); }
export fn isGameOver() bool { return state.game_over; }
export fn isInTerminal() bool { return state.in_terminal; }
export fn getIntroSynthPtr() [*]const u8 { return assets.intro_synth.ptr; }
export fn getIntroSynthLen() usize { return assets.intro_synth.len; }
export fn getBackstoryPtr() [*]const u8 { return assets.backstory.ptr; }
export fn getBackstoryLen() usize { return assets.backstory.len; }
export fn getEndingSynthPtr() [*]const u8 { return assets.ending_synth.ptr; }
export fn getEndingSynthLen() usize { return assets.ending_synth.len; }
export fn getTerminalTickPtr() [*]const u8 { return assets.terminal_tick.ptr; }
export fn getTerminalTickLen() usize { return assets.terminal_tick.len; }
export fn getAirlockDeathPtr() [*]const u8 { return assets.airlock_death.ptr; }
export fn getAirlockDeathLen() usize { return assets.airlock_death.len; }
export fn getElevatorApproachPtr() [*]const u8 { return assets.elevator_approach.ptr; }
export fn getElevatorApproachLen() usize { return assets.elevator_approach.len; }
export fn getElevatorKlonkPtr() [*]const u8 { return assets.elevator_klonk.ptr; }
export fn getElevatorKlonkLen() usize { return assets.elevator_klonk.len; }
export fn getElevatorMovingPtr() [*]const u8 { return assets.elevator_moving.ptr; }
export fn getElevatorMovingLen() usize { return assets.elevator_moving.len; }
export fn getElevatorDeathPtr() [*]const u8 { return assets.elevator_death.ptr; }
export fn getElevatorDeathLen() usize { return assets.elevator_death.len; }
export fn getAlienDeathPtr() [*]const u8 { return assets.alien_death.ptr; }
export fn getAlienDeathLen() usize { return assets.alien_death.len; }

export fn getTapeRewindPtr() [*]const u8 { return assets.tape_rewind.ptr; }
export fn getTapeRewindLen() usize { return assets.tape_rewind.len; }
export fn getTapeClickPtr() [*]const u8 { return assets.tape_click.ptr; }
export fn getTapeClickLen() usize { return assets.tape_click.len; }
export fn getTapeLogPtr() [*]const u8 { return assets.tape_log.ptr; }
export fn getTapeLogLen() usize { return assets.tape_log.len; }
export fn getEvacuateAnnouncementPtr() [*]const u8 { return assets.evacuate_announcement.ptr; }
export fn getEvacuateAnnouncementLen() usize { return assets.evacuate_announcement.len; }

export fn getAlienActive() bool { return state.alien_active; }
export fn getAlienPos() u8 { return @intFromEnum(state.alien_pos); }

export fn tick(dt: f32) void {
    if (state.game_over) return;

    // Spawn logic: 30% chance every minute
    state.spawn_timer += dt;
    if (state.spawn_timer >= 60.0) {
        state.spawn_timer = 0.0;
        // Simple pseudo-random using time/memory address would be better, but we don't have good rng here.
        // We can use a simple counter or just rely on the fact that dt fluctuates slightly?
        // Let's use a Linear Congruential Generator with a seed we update.
        // Or simpler: pass a random number from JS in tick?
        // Let's just assume 30% for now with a naive check.
        // Since we don't have random source, let's ask JS to provide entropy or just make it deterministic for now.
        // Actually, let's implement a simple LCG.
    }
}

// Simple LCG
var rng_state: u32 = 12345;
fn randomFloat() f32 {
    rng_state = rng_state *% 1664525 +% 1013904223;
    return @as(f32, @floatFromInt(rng_state >> 8)) / 16777216.0;
}

export fn getReactionPtr(id: u8) [*]const u8 {
    return switch(id) {
        0 => assets.reaction_0.ptr, 1 => assets.reaction_1.ptr, 2 => assets.reaction_2.ptr, 3 => assets.reaction_3.ptr,
        4 => assets.reaction_4.ptr, 5 => assets.reaction_5.ptr, 6 => assets.reaction_6.ptr, else => assets.reaction_0.ptr
    };
}
export fn getReactionLen(id: u8) usize {
    return switch(id) {
        0 => assets.reaction_0.len, 1 => assets.reaction_1.len, 2 => assets.reaction_2.len, 3 => assets.reaction_3.len,
        4 => assets.reaction_4.len, 5 => assets.reaction_5.len, 6 => assets.reaction_6.len, else => assets.reaction_0.len
    };
}

export fn tickWithSeed(dt: f32, seed: u32) void {
    if (state.game_over) return;
    rng_state = rng_state +% seed; // Mix in entropy from JS

    // Announcement Logic
    state.announcement_timer += dt;
    if (state.announcement_timer >= 90.0) {
        state.announcement_timer = 0.0;
        if (@intFromEnum(state.current_loc) <= 15) {
            playSound(assets.evacuate_announcement.ptr, assets.evacuate_announcement.len, false);
            jsPrint("\n[ INTERCOM: \"Evacuate the station. Oxygen level low.\" ]\n");
        }
    }

    // Rumble Logic - Only in the mine (id >= 17)
    if (!state.rumble_active) {
        state.rumble_timer += dt;
        // Trigger roughly every 120 seconds, only if in the mine
        if (state.rumble_timer >= 120.0 and @intFromEnum(state.current_loc) >= 17) {
             state.rumble_timer = 0.0;
             state.rumble_active = true;
             state.rumble_stage = 1;
             playSound(assets.train_rumble.ptr, assets.train_rumble.len, false);
             jsPrint("\n[ The ground begins to tremble... a deep, growing roar fills the air... ]\n");
        } else if (state.rumble_timer >= 120.0) {
             // Reset timer even if not in mine so it doesn't trigger immediately upon entering
             state.rumble_timer = 0.0;
        }
    } else {
        state.rumble_timer += dt;
        if (state.rumble_stage == 1 and state.rumble_timer >= 15.0) { // Rumble finished
            state.rumble_stage = 2;
            state.rumble_timer = 0.0;
            // Play random reaction
            const r_idx = @as(u8, @intFromFloat(randomFloat() * 7.0));
            const r_ptr = getReactionPtr(r_idx);
            const r_len = getReactionLen(r_idx);
            playSound(r_ptr, r_len, false);
            
            const r_text = switch(r_idx) {
                0 => "What was that?", 1 => "What in the...", 2 => "I wonder what that is.", 3 => "What in the world just happened?",
                4 => "I hope this place doesn't collapse.", 5 => "Is that dust coming from the ceiling?!", 6 => "Wow.", else => "..."
            };
            jsPrint("\nYOU: \""); jsPrint(r_text); jsPrint("\"\n");
        } else if (state.rumble_stage == 2 and state.rumble_timer >= 5.0) {
            state.rumble_active = false;
            state.rumble_stage = 0;
            state.rumble_timer = 0.0;
        }
    }

    // Spawn logic
    state.spawn_timer += dt;
    if (!state.alien_active and state.spawn_timer >= 60.0) {
        state.spawn_timer = 0;
        if (randomFloat() < 0.3) {
            state.alien_active = true;
            state.alien_moves_made = 0;
            state.alien_move_timer = 0.0;
            state.alien_timer = 0.0;
            // Pick random start location
            const loc_idx = @as(usize, @intFromFloat(randomFloat() * 17.0)) % 17;
            state.alien_pos = @enumFromInt(loc_idx);
            playSound(assets.alien_sonar.ptr, assets.alien_sonar.len, false);
        }
    }

    if (state.alien_active) {
        state.alien_timer += dt;
        state.alien_move_timer += dt;
        
        // Move every 10 seconds
        if (state.alien_move_timer >= 10.0) {
            state.alien_move_timer = 0.0;
            state.alien_moves_made += 1;

            if (state.alien_moves_made >= 3) {
                state.alien_active = false; // Disappear after 3 moves (30s total)
            } else {
                // Move to adjacent
                const loc = getLoc(state.alien_pos);
                var valid_moves: [6]?LocationId = [_]?LocationId{null} ** 6;
                var count: usize = 0;
                if (loc.n) |n| { valid_moves[count] = n; count += 1; }
                if (loc.s) |n| { valid_moves[count] = n; count += 1; }
                if (loc.e) |n| { valid_moves[count] = n; count += 1; }
                if (loc.w) |n| { valid_moves[count] = n; count += 1; }
                if (loc.u) |n| { valid_moves[count] = n; count += 1; }
                if (loc.d) |n| { valid_moves[count] = n; count += 1; }

                if (count > 0) {
                    const idx = @as(usize, @intFromFloat(randomFloat() * @as(f32, @floatFromInt(count))));
                    if (valid_moves[idx]) |new_pos| {
                        state.alien_pos = new_pos;
                        playSound(assets.alien_sonar.ptr, assets.alien_sonar.len, false);
                    }
                }
            }
        }

        // Check collision
        if (state.alien_active and state.alien_pos == state.current_loc) {
            triggerSpecialSequence(4); // Alien death sequence
        }
    }
}

export fn setElevatorArrived(val: bool) void { state.elevator_arrived = val; state.elevator_summoning = false; }
export fn arriveAtMine() void {
    state.elevator_moving_down = false;
    state.elevator_level = 1;
    changeLocation(.mine_elevator_lobby);
    jsPrint("\nThe elevator shudders to a halt. The doors open to a dusty cavern.\n");
}

export fn arriveAtLobby() void {
    state.elevator_moving_down = false;
    state.elevator_level = 0;
    changeLocation(.elevator_lobby_beta); // Return to Beta lobby? Or Alpha? Beta is closer to Reactor.
    jsPrint("\nThe elevator chimes politely. The doors open to the polished corridors.\n");
}

export fn setGameOver() void { state.game_over = true; }

const locations = [_]Location{
    .{
        .id = .observation_dome,
        .name = "Observation Dome",
        .description = "A majestic glass dome. The Earth hangs like a blue marble. Frost patterns crawl across the edges. An emergency airlock wheel is here.",
        .bg_sound = assets.observation_dome,
        .s = .comms_array,
    },
    .{
        .id = .comms_array,
        .name = "Communications Array",
        .description = "Towering racks of vacuum tubes. The equipment here is mostly passive reception gear.",
        .item_description = "A complex control board with gold contacts.",
        .bg_sound = assets.comms_array,
        .n = .observation_dome,
        .e = .security_hub,
    },
    .{
        .id = .security_hub,
        .name = "Security Hub",
        .description = "Banks of CRT monitors show grainy views of empty corridors. A single central terminal is active here.",
        .bg_sound = assets.security_hub,
        .w = .comms_array,
        .s = .elevator_lobby_alpha,
    },
    .{
        .id = .elevator_lobby_alpha,
        .name = "Elevator Lobby Alpha",
        .description = "Polished aluminium panels. A heavy elevator door is here next to a call button. A maintenance ladder leads down.",
        .bg_sound = assets.elevator_lobby_alpha,
        .n = .security_hub,
        .d = .mess_hall,
    },
    .{
        .id = .mess_hall,
        .name = "Mess Hall",
        .description = "Teal Formica tables. A ghostly tune drifts from a cracked intercom. A ladder leads up.",
        .bg_sound = assets.mess_hall,
        .u = .elevator_lobby_alpha,
        .s = .sleeping_pods,
    },
    .{
        .id = .sleeping_pods,
        .name = "Sleeping Pods",
        .description = "Tiered bunks carved into the rock. Warm air smells of stale laundry.",
        .item_description = "A heavy high-capacity battery cell.",
        .bg_sound = assets.sleeping_pods,
        .n = .mess_hall,
        .e = .medical_lab,
    },
    .{
        .id = .medical_lab,
        .name = "Medical Lab",
        .description = "Surgical lamps and rows of glass vials. A ladder leads down.",
        .bg_sound = assets.medical_lab,
        .w = .sleeping_pods,
        .s = .elevator_lobby_beta,
    },
    .{
        .id = .elevator_lobby_beta,
        .name = "Elevator Lobby Beta",
        .description = "Bare rock walls. A strobe light flashes near the elevator doors. A ladder leads up.",
        .bg_sound = assets.elevator_lobby_beta,
        .n = .medical_lab,
        .d = .main_reactor,
    },
    .{
        .id = .main_reactor,
        .name = "Main Reactor",
        .description = "A massive sphere pulses with cerenkov-blue light. A ladder leads up.",
        .bg_sound = assets.main_reactor,
        .u = .elevator_lobby_beta,
        .e = .fuel_storage,
    },
    .{
        .id = .fuel_storage,
        .name = "Fuel Storage",
        .description = "Cold storage for lead-lined canisters. Silence broken by groaning pipes.",
        .bg_sound = assets.fuel_storage,
        .w = .main_reactor,
        .s = .battery_bank,
    },
    .{
        .id = .battery_bank,
        .name = "Battery Bank",
        .description = "Floor-to-ceiling racks of glass batteries. Smell of electrolytes.",
        .bg_sound = assets.battery_bank,
        .n = .fuel_storage,
        .w = .maintenance_tunnels,
    },
    .{
        .id = .maintenance_tunnels,
        .name = "Maintenance Tunnels",
        .description = "Maze of hissing steam pipes. Metal grating floor.",
        .bg_sound = assets.maintenance_tunnels,
        .e = .battery_bank,
        .u = .cargo_loading,
    },
    .{
        .id = .cargo_loading,
        .name = "Cargo Loading",
        .description = "Massive hangar. Yellow forklift near urgency crates. A ladder leads down.",
        .bg_sound = assets.cargo_loading,
        .d = .maintenance_tunnels,
        .w = .oxygen_scrubbers,
    },
    .{
        .id = .oxygen_scrubbers,
        .name = "Oxygen Scrubbers",
        .description = "Giant glass cylinders filled with bubbling green algae. The air is fresh but the monitoring station is dark.",
        .bg_sound = assets.oxygen_scrubbers,
        .e = .cargo_loading,
        .n = .launch_control,
    },
    .{
        .id = .launch_control,
        .name = "Launch Control",
        .description = "Raised dais overlooks the hangar. Circular radar screen sweeps endlessly.",
        .bg_sound = assets.launch_control,
        .s = .oxygen_scrubbers,
        .n = .escape_pod,
    },
    .{
        .id = .escape_pod,
        .name = "Escape Pod Module",
        .description = "Sphere of polished steel. Quilted leather interior.",
        .bg_sound = assets.escape_pod,
        .s = .launch_control,
    },
    .{
        .id = .elevator_interior,
        .name = "Elevator Interior",
        .description = "Quilted metal padding. A single 'LOWER LEVELS' button is here.",
        .bg_sound = assets.elevator_moving,
    },
    // Mine Rooms
    .{
        .id = .mine_elevator_lobby,
        .name = "Mine Level: Lobby",
        .description = "Rough hewn rock walls reinforced with rusty steel beams. The elevator shaft goes up. Dust motes dance in the air.",
        .bg_sound = assets.elevator_lobby_beta, // Reuse or silence? Let's reuse beta for industrial feel
        .e = .work_room,
        .d = .bunk_room, // Stairs down
    },
    .{
        .id = .work_room,
        .name = "Mine Level: Work Room",
        .description = "A cluttered workspace. Blueprints scattered on the floor. A heavy desk sits against the wall with a tape recorder on it. A small, pixelated picture hangs on the wall.",
        .bg_sound = assets.work_room_bg,
        .w = .mine_elevator_lobby,
    },
    .{
        .id = .bunk_room,
        .name = "Mine Level: Bunk Room",
        .description = "Cramped living quarters. Triple-stacked bunk beds. A reading lamp flickers over a pile of old magazines.",
        .bg_sound = assets.sleeping_pods,
        .u = .mine_elevator_lobby, // Stairs up
        .s = .shower_area,
    },
    .{
        .id = .shower_area,
        .name = "Mine Level: Showers",
        .description = "Communal showers. The tiles are cracked and yellowed. Water drips rhythmically.",
        .bg_sound = assets.medical_lab, // Reuse sterile/watery sound
        .n = .bunk_room,
        .e = .toilet_room,
    },
    .{
        .id = .toilet_room,
        .name = "Mine Level: Toilets",
        .description = "A row of industrial toilets. The smell is ancient and metallic.",
        .bg_sound = assets.airlock_hiss, // Reuse hiss for pipe noise
        .w = .shower_area,
        .d = .mine_storage, // Stairs down
    },
    .{
        .id = .crusher_room,
        .name = "Stone Crushing Room",
        .description = "Dominated by a massive, silent crushing machine. Conveyor belts sit idle. A dark opening leads to the tunnels.",
        .bg_sound = assets.maintenance_tunnels,
        .w = .mine_storage,
        .s = .tunnel_entrance,
    },
    .{
        .id = .tunnel_entrance,
        .name = "Deep Tunnel Entrance",
        .description = "The lights end here. A pitch-black tunnel descends into the crust. You hear strange robotic sounds echoing from the deep.",
        .bg_sound = assets.deep_tunnel,
        .n = .crusher_room,
    },
    .{
        .id = .mine_storage,
        .name = "Mine Level: Storage",
        .description = "Crates of mining explosives and pickaxes. A massive industrial lever is mounted on the wall. A heavy blast door leads to the crushing room.",
        .bg_sound = assets.cargo_loading,
        .u = .toilet_room, // Stairs up
        .e = .crusher_room,
    },
};

fn getLoc(id: LocationId) *const Location { return &locations[@intFromEnum(id)]; }
fn jsPrint(text: []const u8) void { printText(text.ptr, text.len); }
fn jsTerminal(text: []const u8) void { printTerminal(text.ptr, text.len); }

fn changeLocation(id: LocationId) void {
    state.current_loc = id;
    state.visited[@intFromEnum(id)] = true;
    
    // Check alien collision on entry
    if (state.alien_active and state.alien_pos == state.current_loc) {
        triggerSpecialSequence(4);
        return;
    }

    const loc = getLoc(id);
    stopLoopingSounds();
    playSound(loc.bg_sound.ptr, loc.bg_sound.len, true);
    jsPrint("\n--- "); jsPrint(loc.name); jsPrint(" ---\n");
    jsPrint(loc.description); jsPrint("\n");
    const item = if (@intFromEnum(id) < 17) state.items_at_loc[@intFromEnum(id)] else null;
    if (item) |i| { jsPrint("You see a "); jsPrint(i.name()); jsPrint(" here.\n"); }
    jsPrint("\nExits:\n");
    var has_exits = false;
    if (loc.n) |nid| { jsPrint("- North: "); jsPrint(getLoc(nid).name); jsPrint("\n"); has_exits = true; }
    if (loc.s) |nid| { jsPrint("- South: "); jsPrint(getLoc(nid).name); jsPrint("\n"); has_exits = true; }
    if (loc.e) |nid| { jsPrint("- East: "); jsPrint(getLoc(nid).name); jsPrint("\n"); has_exits = true; }
    if (loc.w) |nid| { jsPrint("- West: "); jsPrint(getLoc(nid).name); jsPrint("\n"); has_exits = true; }
    if (loc.u) |nid| { jsPrint("- Up: "); jsPrint(getLoc(nid).name); jsPrint("\n"); has_exits = true; }
    if (loc.d) |nid| { jsPrint("- Down: "); jsPrint(getLoc(nid).name); jsPrint("\n"); has_exits = true; }
    if (!has_exits) jsPrint("None.\n");
    jsPrint("\n");
    if (id == .observation_dome) jsPrint("[ HINT: You could 'unlock airlock' here. ]\n");
    if (id == .elevator_lobby_alpha or id == .elevator_lobby_beta or id == .mine_elevator_lobby) {
        if (!state.elevator_arrived) {
            jsPrint("[ HINT: You can 'summon elevator' here. ]\n");
        } else {
            jsPrint("[ HINT: The doors are open. You can 'enter' the elevator. ]\n");
        }
    }
    if (id == .elevator_interior and !state.elevator_moving_down) {
        if (state.elevator_level == 1) {
            jsPrint("[ HINT: You can 'push button' to ascend. ]\n");
        } else {
            jsPrint("[ HINT: You can 'push button' to descend. ]\n");
        }
    }
    if (id == .work_room) jsPrint("[ HINT: You can 'play tape', 'rewind tape', or 'open drawer' here. ]\n");
    if (id == .toilet_room) jsPrint("[ HINT: You can 'flush' the toilet. ]\n");
    if (id == .crusher_room) jsPrint("[ HINT: You can try to 'start machine'. ]\n");
    if (id == .bunk_room) jsPrint("[ HINT: You can 'sleep' or 'read'. ]\n");

    // Missing part hints
    if (id == .escape_pod and !state.pod_interface_ready) jsPrint("The pod's nav system is offline. It looks like it's missing the 'CONTROL BOARD'.\n");
    if (id == .escape_pod and state.pod_interface_ready and state.batteries_inserted < 1) {
        jsPrint("The battery bank is empty. It requires 1 High-Capacity Battery.\n");
    }
}

export fn init() void {
    state.items_at_loc[@intFromEnum(LocationId.comms_array)] = .control_board;
    state.items_at_loc[@intFromEnum(LocationId.sleeping_pods)] = .battery;
    
    // Generate shuttle code
    state.shuttle_code[0] = @as(u8, @intFromFloat(randomFloat() * 26.0)) + 'A';
    state.shuttle_code[1] = @as(u8, @intFromFloat(randomFloat() * 26.0)) + 'A';
    state.shuttle_code[2] = @as(u8, @intFromFloat(randomFloat() * 26.0)) + 'A';
    state.shuttle_code[3] = @as(u8, @intFromFloat(randomFloat() * 26.0)) + 'A';

    jsPrint("Welcome to Lunar Retro-Alpha.\nEscape the 1955 Moon Base.\n");
    changeLocation(.observation_dome);
}

var input_buffer: [256]u8 = undefined;
export fn getInputBuffer() [*]u8 { return &input_buffer; }

export fn onCommand(len: usize) void {
    if (state.game_over) return;
    rng_state = rng_state +% len; // Add command entropy
    const cmd_full = input_buffer[0..len];
    var it = std.mem.tokenizeAny(u8, cmd_full, " ");
    const cmd = it.next() orelse return;
    const arg = it.next();

    if (state.in_terminal) {
        if (std.mem.eql(u8, cmd, "exit") or std.mem.eql(u8, cmd, "quit") or std.mem.eql(u8, cmd, "logout")) {
            state.in_terminal = false;
            jsPrint("\n[ TERMINAL SESSION TERMINATED ]\n");
            changeLocation(state.current_loc);
            return;
        }
        if (std.mem.eql(u8, cmd, "temp")) {
            jsTerminal("\n> INTERNAL TEMPERATURE: 19.4 C\n> EXTERNAL TEMPERATURE: -153.2 C\n> THERMAL REGULATORS: NOMINAL\n");
        } else if (std.mem.eql(u8, cmd, "air")) {
            jsTerminal("\n> OXYGEN CONCENTRATION: 18.2%\n> CARBON DIOXIDE: 0.04%\n> SCRUBBER STATUS: ACTIVE\n");
        } else if (std.mem.eql(u8, cmd, "water")) {
            jsTerminal("\n> POTABLE WATER: 412 LITERS\n> RECYCLING EFFICIENCY: 94%\n> RESERVE TANKS: STABLE\n");
        } else if (std.mem.eql(u8, cmd, "power")) {
            if (state.reactor_powered) {
                jsTerminal("\n> SOURCE: MAIN REACTOR\n> STATUS: ONLINE / STABLE\n> GRID LOAD: 42%\n");
                if (state.mine_powered) {
                    jsTerminal("> MINE AUXILIARY: ACTIVE\n");
                } else {
                    jsTerminal("> MINE AUXILIARY: OFFLINE\n");
                }
            } else {
                jsTerminal("\n> SOURCE: EMERGENCY BATTERY\n> STATUS: LOW POWER MODE\n> DRAIN RATE: CRITICAL\n");
            }
        } else if (std.mem.eql(u8, cmd, "activate") and arg != null and (std.mem.eql(u8, arg.?, "generator") or std.mem.eql(u8, arg.?, "mine"))) {
            if (state.reactor_powered) {
                 state.mine_powered = true;
                 jsTerminal("\n> INITIATING HANDSHAKE...\n> MINE GENERATOR SYNCED.\n> ELEVATOR SAFETY LOCKS: DISENGAGED.\n");
            } else {
                 jsTerminal("\n> ERROR: INSUFFICIENT POWER TO ACTIVATE REMOTE SUBSYSTEMS.\n");
            }
        } else if (std.mem.eql(u8, cmd, "help")) {
            jsTerminal("\nAVAILABLE DIAGNOSTICS: TEMP, AIR, WATER, POWER, ACTIVATE GENERATOR, EXIT\n");
        } else {
            jsTerminal("\nCOMMAND NOT RECOGNIZED. TYPE 'HELP' FOR OPTIONS.\n");
        }
        return;
    }

    if (std.mem.eql(u8, cmd, "terminal")) {
        if (state.current_loc != .security_hub) {
            jsPrint("There is no active terminal here. The Security Hub might have one.\n");
            return;
        }
        state.in_terminal = true;
        jsTerminal("\n--- MUTHUR 6000 CENTRAL INTERFACE ---\n");
        jsTerminal("READY FOR INPUT: TEMP, AIR, WATER, POWER, EXIT\n");
    } else if (std.mem.eql(u8, cmd, "summon") or (std.mem.eql(u8, cmd, "press") and arg != null and std.mem.eql(u8, arg.?, "button"))) {
        if (state.current_loc == .elevator_lobby_alpha or state.current_loc == .elevator_lobby_beta or state.current_loc == .mine_elevator_lobby) {
            if (state.elevator_arrived) { jsPrint("The elevator is already here.\n"); return; }
            if (state.elevator_summoning) { jsPrint("The elevator is on its way.\n"); return; }
            playSound(assets.elevator_button.ptr, assets.elevator_button.len, false);
            state.elevator_summoning = true; triggerSpecialSequence(1);
            jsPrint("You press the button. A distant hum begins to vibrate through the floor.\n");
        } else jsPrint("There is no elevator here.\n");
    } else if (std.mem.eql(u8, cmd, "enter") or std.mem.eql(u8, cmd, "in")) {
        if (state.current_loc == .elevator_lobby_alpha or state.current_loc == .elevator_lobby_beta or state.current_loc == .mine_elevator_lobby) {
            if (!state.elevator_arrived) { jsPrint("The elevator is not here.\n"); return; }
            if (state.current_loc == .mine_elevator_lobby) {
                state.elevator_level = 1;
            } else {
                state.elevator_level = 0;
            }
            jsPrint("You step into the elevator.\n"); changeLocation(.elevator_interior);
        } else jsPrint("There is nothing to enter here.\n");
    } else if (std.mem.eql(u8, cmd, "push") or std.mem.eql(u8, cmd, "press")) {
        if (state.current_loc == .elevator_interior and !state.elevator_moving_down) {
            playSound(assets.elevator_button.ptr, assets.elevator_button.len, false);
            state.elevator_moving_down = true;
            jsPrint("The doors slide shut. The elevator begins to move.\n");
            
            if (state.elevator_level == 0) { // Top -> Bottom
                if (state.mine_powered) {
                    triggerSpecialSequence(5); // Mine arrival
                } else {
                    triggerSpecialSequence(2); // Death
                }
            } else { // Bottom -> Top
                triggerSpecialSequence(7); // Ascend
            }
        } else jsPrint("Nothing to push here.\n");
    } else if (std.mem.eql(u8, cmd, "flush")) {
        if (state.current_loc == .toilet_room) {
            // Random flush sound 0-7 using LCG
            const seed = @as(usize, @intFromFloat(randomFloat() * 8.0)) % 8;
            const s = switch(seed) {
                0 => assets.toilet_flush_0, 1 => assets.toilet_flush_1, 2 => assets.toilet_flush_2, 3 => assets.toilet_flush_3,
                4 => assets.toilet_flush_4, 5 => assets.toilet_flush_5, 6 => assets.toilet_flush_6, 7 => assets.toilet_flush_7,
                else => assets.toilet_flush_0
            };
            playSound(s.ptr, s.len, false);
            jsPrint("WHOOSH! You flush the toilet.\n");
        } else jsPrint("No toilet here.\n");
    } else if (std.mem.eql(u8, cmd, "start")) {
        if (state.current_loc == .crusher_room) {
            playSound(assets.crusher_broken.ptr, assets.crusher_broken.len, false);
            jsPrint("The machine coughs and sputters. It sounds broken.\n");
        } else jsPrint("Nothing to start here.\n");
    } else if (std.mem.eql(u8, cmd, "sleep")) {
        if (state.current_loc == .bunk_room) {
            playSound(assets.sleep_sounds.ptr, assets.sleep_sounds.len, false);
            jsPrint("You lay down for a moment. The bed is hard but the rest is welcome.\n");
        } else jsPrint("Not a good place to sleep.\n");
    } else if (std.mem.eql(u8, cmd, "read")) {
        if (state.current_loc == .bunk_room) {
            jsPrint("You pick up a magazine. 'Popular Mechanics: July 1954'. It details flying cars.\n");
        } else jsPrint("Nothing to read here.\n");
    } else if (std.mem.eql(u8, cmd, "play")) {
        if (state.current_loc == .work_room) {
             playSound(assets.tape_click.ptr, assets.tape_click.len, false);
             if (!state.tape_rewound) {
                 jsPrint("The tape heads spin for a second then stop. It needs rewinding.\n");
             } else {
                 playSound(assets.tape_log.ptr, assets.tape_log.len, false);
                 jsPrint("Playing log...\n");
                 state.tape_rewound = false;
             }
        } else jsPrint("Nothing to play here.\n");
    } else if (std.mem.eql(u8, cmd, "rewind")) {
        if (state.current_loc == .work_room) {
             playSound(assets.tape_rewind.ptr, assets.tape_rewind.len, false);
             jsPrint("Rewinding tape...\n");
             state.tape_rewound = true;
        } else jsPrint("Nothing to rewind here.\n");
    } else if (std.mem.eql(u8, cmd, "pull")) {
        if (state.current_loc == .mine_storage) {
            if (arg != null and std.mem.eql(u8, arg.?, "lever")) {
                if (state.lever_pulled) {
                    jsPrint("The lever is already pulled down. The lights are off.\n");
                } else {
                    playSound(assets.lever_clonk.ptr, assets.lever_clonk.len, false);
                    state.lever_pulled = true;
                    jsPrint("KLONK. The lights flicker and die. Total darkness engulfs the mine.\n");
                    const seed = @as(usize, @intFromFloat(randomFloat() * 4.0));
                    const s = switch(seed) {
                        0 => assets.lever_bad_0, 1 => assets.lever_bad_1, 2 => assets.lever_bad_2, 3 => assets.lever_bad_3, else => assets.lever_bad_0
                    };
                    playSound(s.ptr, s.len, false);
                    const txt = switch(seed) {
                        0 => "Uh oh.", 1 => "That wasn't good.", 2 => "...", 3 => "What happened to the lights?", else => "..."
                    };
                    jsPrint("YOU: \""); jsPrint(txt); jsPrint("\"\n");
                }
            } else jsPrint("Pull what?\n");
        } else jsPrint("Nothing to pull here.\n");
    } else if (std.mem.eql(u8, cmd, "push")) {
        if (state.current_loc == .mine_storage) {
            if (arg != null and std.mem.eql(u8, arg.?, "lever")) {
                if (!state.lever_pulled) {
                    jsPrint("The lever is already pushed up. The lights are on.\n");
                } else {
                    playSound(assets.lever_clonk.ptr, assets.lever_clonk.len, false);
                    state.lever_pulled = false;
                    jsPrint("KLONK. A generator hums to life. The lights flicker back on.\n");
                    playSound(assets.reactor_ignition_roar.ptr, assets.reactor_ignition_roar.len, false);
                    const seed = @as(usize, @intFromFloat(randomFloat() * 3.0));
                    const s = switch(seed) {
                        0 => assets.lever_good_0, 1 => assets.lever_good_1, 2 => assets.lever_good_2, else => assets.lever_good_0
                    };
                    playSound(s.ptr, s.len, false);
                    const txt = switch(seed) {
                        0 => "That's better.", 1 => "Alright.", 2 => "Much better.", else => "..."
                    };
                    jsPrint("YOU: \""); jsPrint(txt); jsPrint("\"\n");
                }
            } else jsPrint("Push what?\n");
        } else jsPrint("Nothing to push here.\n");
    } else if (std.mem.eql(u8, cmd, "open") and arg != null and std.mem.eql(u8, arg.?, "drawer")) {
        if (state.current_loc == .work_room) {
            playSound(assets.drawer_open.ptr, assets.drawer_open.len, false);
            jsPrint("You slide the drawer open. Inside is a manual: 'Operating the Express48 Type B Mining Shuttle'.\n");
            jsPrint("Handwritten on the cover is a code: ");
            jsPrint(&state.shuttle_code); jsPrint("\n");
        } else jsPrint("No drawer here.\n");
    } else if (std.mem.eql(u8, cmd, "look") and arg != null and std.mem.eql(u8, arg.?, "picture")) {
        if (state.current_loc == .work_room) {
            triggerSpecialSequence(6);
            jsPrint("You peer closely at the pixelated masterpiece.\n");
        } else jsPrint("No picture here.\n");
    } else if (std.mem.eql(u8, cmd, "unlock") and arg != null and std.mem.eql(u8, arg.?, "airlock")) {
        if (state.current_loc == .observation_dome) {
            playSound(assets.airlock_death.ptr, assets.airlock_death.len, false);
            triggerSpecialSequence(3);
        } else jsPrint("There is no airlock here.\n");
    } else if (std.mem.eql(u8, cmd, "look") or std.mem.eql(u8, cmd, "l")) {
        changeLocation(state.current_loc);
    } else if (std.mem.eql(u8, cmd, "examine") or std.mem.eql(u8, cmd, "x")) {
        const item = if (@intFromEnum(state.current_loc) < 17) state.items_at_loc[@intFromEnum(state.current_loc)] else null;
        if (item) |_| { jsPrint(getLoc(state.current_loc).item_description); jsPrint("\n"); }
        else jsPrint("There's nothing here to examine closely.\n");
    } else if (std.mem.eql(u8, cmd, "go") or std.mem.eql(u8, cmd, "n") or std.mem.eql(u8, cmd, "s") or std.mem.eql(u8, cmd, "e") or std.mem.eql(u8, cmd, "w") or std.mem.eql(u8, cmd, "u") or std.mem.eql(u8, cmd, "d") or std.mem.eql(u8, cmd, "north") or std.mem.eql(u8, cmd, "south") or std.mem.eql(u8, cmd, "east") or std.mem.eql(u8, cmd, "west") or std.mem.eql(u8, cmd, "up") or std.mem.eql(u8, cmd, "down")) {
        if (state.lever_pulled and @intFromEnum(state.current_loc) >= 17) {
            jsPrint("It's too dark to see where you're going! You need to turn the lights back on.\n");
            return;
        }
        const dir_str = if (std.mem.eql(u8, cmd, "go")) (arg orelse { jsPrint("Go where?\n"); return; }) else cmd;
        const loc = getLoc(state.current_loc);
        const next_id: ?LocationId = if (std.mem.eql(u8, dir_str, "north") or std.mem.eql(u8, dir_str, "n")) loc.n
        else if (std.mem.eql(u8, dir_str, "south") or std.mem.eql(u8, dir_str, "s")) loc.s
        else if (std.mem.eql(u8, dir_str, "east") or std.mem.eql(u8, dir_str, "e")) loc.e
        else if (std.mem.eql(u8, dir_str, "west") or std.mem.eql(u8, dir_str, "w")) loc.w
        else if (std.mem.eql(u8, dir_str, "up") or std.mem.eql(u8, dir_str, "u")) loc.u
        else if (std.mem.eql(u8, dir_str, "down") or std.mem.eql(u8, dir_str, "d")) loc.d
        else null;
        if (next_id) |nid| changeLocation(nid) else jsPrint("You can't go that way.\n");
    } else if (std.mem.eql(u8, cmd, "take") or std.mem.eql(u8, cmd, "get") or std.mem.eql(u8, cmd, "t")) {
        const item = if (@intFromEnum(state.current_loc) < 17) state.items_at_loc[@intFromEnum(state.current_loc)] else null;
        if (item) |i| { state.setItem(i, true); state.items_at_loc[@intFromEnum(state.current_loc)] = null;
            playSound(assets.item_pickup.ptr, assets.item_pickup.len, false);
            jsPrint("You took the "); jsPrint(i.name()); jsPrint(".\n");
        } else jsPrint("Nothing here to take.\n");
    } else if (std.mem.eql(u8, cmd, "inventory") or std.mem.eql(u8, cmd, "i")) {
        jsPrint("Inventory: "); var found = false;
        inline for (std.meta.fields(Item)) |f| { const i: Item = @enumFromInt(f.value); if (state.hasItem(i)) { if (found) jsPrint(", "); jsPrint(i.name()); found = true; } }
        if (!found) jsPrint("Empty"); jsPrint("\n");
    } else if (std.mem.eql(u8, cmd, "use") or std.mem.eql(u8, cmd, "insert") or std.mem.eql(u8, cmd, "install")) {
        const loc = state.current_loc;
        const target = arg orelse "";
        var handled = false;
        if (std.mem.eql(u8, target, "board") or std.mem.eql(u8, target, "") or std.mem.eql(u8, target, "item")) {
            if (state.hasItem(.control_board)) {
                if (loc == .escape_pod) {
                    state.setItem(.control_board, false);
                    state.pod_interface_ready = true;
                    playSound(assets.pod_systems_active.ptr, assets.pod_systems_active.len, false);
                    jsPrint("Pod systems synced. Control Board installed.\n");
                    handled = true;
                }
            }
        }
        if (!handled and (std.mem.eql(u8, target, "battery") or std.mem.eql(u8, target, ""))) {
            if (loc == .escape_pod) {
                if (state.hasItem(.battery)) {
                    state.setItem(.battery, false);
                    state.batteries_inserted = 1;
                    playSound(assets.battery_insert.ptr, assets.battery_insert.len, false);
                    jsPrint("Battery installed. Systems charging...\n");
                    handled = true;
                }
            }
        }
        if (!handled) jsPrint("Nothing to install here or you're missing the required part.\n");
        if (state.pod_interface_ready and state.batteries_inserted >= 1) {
            state.game_over = true;
            jsPrint("\n*** ALL SYSTEMS GO! ***\n");
            jsPrint("You strap in and hit the launch button. The pod blasts off toward Earth!\n\n");
            jsPrint(
                \\          .
                \\         / \
                \\        |   |
                \\        |   |
                \\       /     \
                \\      |_______|
                \\     /         \
                \\    |   RETRO   |
                \\    |   ALPHA   |
                \\    |___________|
                \\        | | |
                \\        | | |
                \\       /  |  \
                \\      /   |   \
                \\
                \\   FAREWELL LUNAR BASE 1955
                \\
            );
            jsPrint("\nYOU ESCAPED THE MOON!\n");
        }
    } else if (std.mem.eql(u8, cmd, "help")) {
        jsPrint("Commands: look (l), go [dir], take (t), inventory (i), install [board/battery], examine (x), terminal, summon elevator, help\n");
    } else { jsPrint("Unknown command: "); jsPrint(cmd); jsPrint("\n"); }
}