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
};

const Item = enum {
    logic_board_a,
    control_board_b,
    power_board_c,
    interface_board_d,
    battery_1,
    battery_2,
    battery_3,
    battery_4,

    fn name(self: Item) []const u8 {
        return switch (self) {
            .logic_board_a => "Logic Board A",
            .control_board_b => "Control Board B (Launch Controller)",
            .power_board_c => "Power Board C (Generator Module)",
            .interface_board_d => "Interface Board D (Pod Link)",
            .battery_1 => "High-Capacity Battery 1",
            .battery_2 => "High-Capacity Battery 2",
            .battery_3 => "High-Capacity Battery 3",
            .battery_4 => "High-Capacity Battery 4",
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
    inventory: [8]bool = [_]bool{false} ** 8,
    items_at_loc: [17]?Item = [_]?Item{null} ** 17,
    visited: [17]bool = [_]bool{false} ** 17,
    reactor_powered: bool = false,
    launch_computer_active: bool = false,
    pod_interface_ready: bool = false,
    batteries_inserted: u4 = 0,
    elevator_arrived: bool = false,
    elevator_summoning: bool = false,
    elevator_moving_down: bool = false,
    in_terminal: bool = false,
    game_over: bool = false,

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

export fn setElevatorArrived(val: bool) void { state.elevator_arrived = val; state.elevator_summoning = false; }
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
        .description = "Towering racks of vacuum tubes. A terminal console is active here.",
        .item_description = "Logic Board A: Gold contacts still shine.",
        .bg_sound = assets.comms_array,
        .n = .observation_dome,
        .e = .security_hub,
    },
    .{
        .id = .security_hub,
        .name = "Security Hub",
        .description = "Banks of CRT monitors show grainy views of empty corridors. A terminal is here.",
        .item_description = "Control Board B: Black polymer shell.",
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
        .item_description = "Logic Board A: Hidden in the toaster.",
        .bg_sound = assets.mess_hall,
        .u = .elevator_lobby_alpha,
        .s = .sleeping_pods,
    },
    .{
        .id = .sleeping_pods,
        .name = "Sleeping Pods",
        .description = "Tiered bunks carved into the rock. Warm air smells of stale laundry.",
        .item_description = "Battery 1: Lead-acid cell.",
        .bg_sound = assets.sleeping_pods,
        .n = .mess_hall,
        .e = .medical_lab,
    },
    .{
        .id = .medical_lab,
        .name = "Medical Lab",
        .description = "Surgical lamps and rows of glass vials. A ladder leads down.",
        .item_description = "Battery 2: Radiation-shielded.",
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
        .item_description = "Power Board C: Handles high-voltage.",
        .bg_sound = assets.main_reactor,
        .u = .elevator_lobby_beta,
        .e = .fuel_storage,
    },
    .{
        .id = .fuel_storage,
        .name = "Fuel Storage",
        .description = "Cold storage for lead-lined canisters. Silence broken by groaning pipes.",
        .item_description = "Control Board B: Oversized capacitors.",
        .bg_sound = assets.fuel_storage,
        .w = .main_reactor,
        .s = .battery_bank,
    },
    .{
        .id = .battery_bank,
        .name = "Battery Bank",
        .description = "Floor-to-ceiling racks of glass batteries. Smell of electrolytes.",
        .item_description = "Battery 3: Lithium-moon-dust hybrid.",
        .bg_sound = assets.battery_bank,
        .n = .fuel_storage,
        .w = .maintenance_tunnels,
    },
    .{
        .id = .maintenance_tunnels,
        .name = "Maintenance Tunnels",
        .description = "Maze of hissing steam pipes. Metal grating floor.",
        .item_description = "Power Board C: Warm to the touch.",
        .bg_sound = assets.maintenance_tunnels,
        .e = .battery_bank,
        .u = .cargo_loading,
    },
    .{
        .id = .cargo_loading,
        .name = "Cargo Loading",
        .description = "Massive hangar. Yellow forklift near urgency crates. A ladder leads down.",
        .item_description = "Battery 4: Marked MAX LOAD.",
        .bg_sound = assets.cargo_loading,
        .d = .maintenance_tunnels,
        .w = .oxygen_scrubbers,
    },
    .{
        .id = .oxygen_scrubbers,
        .name = "Oxygen Scrubbers",
        .description = "Giant glass cylinders filled with bubbling green algae. Terminal active.",
        .item_description = "Interface Board D: Complex 1955-era multi-pin.",
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
};

fn getLoc(id: LocationId) *const Location { return &locations[@intFromEnum(id)]; }
fn jsPrint(text: []const u8) void { printText(text.ptr, text.len); }
fn jsTerminal(text: []const u8) void { printTerminal(text.ptr, text.len); }

fn changeLocation(id: LocationId) void {
    state.current_loc = id;
    state.visited[@intFromEnum(id)] = true;
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
    if (id == .elevator_lobby_alpha or id == .elevator_lobby_beta) {
        if (!state.elevator_arrived) {
            jsPrint("[ HINT: You can 'summon elevator' here. ]\n");
        } else {
            jsPrint("[ HINT: The doors are open. You can 'enter' the elevator. ]\n");
        }
    }
    if (id == .elevator_interior and !state.elevator_moving_down) jsPrint("[ HINT: You can 'push button' to descend. ]\n");
}

export fn init() void {
    state.items_at_loc[@intFromEnum(LocationId.mess_hall)] = .logic_board_a;
    state.items_at_loc[@intFromEnum(LocationId.fuel_storage)] = .control_board_b;
    state.items_at_loc[@intFromEnum(LocationId.maintenance_tunnels)] = .power_board_c;
    state.items_at_loc[@intFromEnum(LocationId.oxygen_scrubbers)] = .interface_board_d;
    state.items_at_loc[@intFromEnum(LocationId.sleeping_pods)] = .battery_1;
    state.items_at_loc[@intFromEnum(LocationId.medical_lab)] = .battery_2;
    state.items_at_loc[@intFromEnum(LocationId.battery_bank)] = .battery_3;
    state.items_at_loc[@intFromEnum(LocationId.cargo_loading)] = .battery_4;
    jsPrint("Welcome to Lunar Retro-Alpha.\nEscape the 1955 Moon Base.\n");
    changeLocation(.observation_dome);
}

var input_buffer: [256]u8 = undefined;
export fn getInputBuffer() [*]u8 { return &input_buffer; }

export fn onCommand(len: usize) void {
    if (state.game_over) return;
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
            } else {
                jsTerminal("\n> SOURCE: EMERGENCY BATTERY\n> STATUS: LOW POWER MODE\n> DRAIN RATE: CRITICAL\n");
            }
        } else if (std.mem.eql(u8, cmd, "help")) {
            jsTerminal("\nAVAILABLE DIAGNOSTICS: TEMP, AIR, WATER, POWER, EXIT\n");
        } else {
            jsTerminal("\nCOMMAND NOT RECOGNIZED. TYPE 'HELP' FOR OPTIONS.\n");
        }
        return;
    }

    if (std.mem.eql(u8, cmd, "terminal")) {
        state.in_terminal = true;
        jsTerminal("\n--- MUTHUR 6000 CENTRAL INTERFACE ---\n");
        jsTerminal("READY FOR INPUT: TEMP, AIR, WATER, POWER, EXIT\n");
    } else if (std.mem.eql(u8, cmd, "summon") or (std.mem.eql(u8, cmd, "press") and arg != null and std.mem.eql(u8, arg.?, "button"))) {
        if (state.current_loc == .elevator_lobby_alpha or state.current_loc == .elevator_lobby_beta) {
            if (state.elevator_arrived) { jsPrint("The elevator is already here.\n"); return; }
            if (state.elevator_summoning) { jsPrint("The elevator is on its way.\n"); return; }
            playSound(assets.elevator_button.ptr, assets.elevator_button.len, false);
            state.elevator_summoning = true; triggerSpecialSequence(1);
            jsPrint("You press the button. A distant hum begins to vibrate through the floor.\n");
        } else jsPrint("There is no elevator here.\n");
    } else if (std.mem.eql(u8, cmd, "enter") or std.mem.eql(u8, cmd, "in")) {
        if (state.current_loc == .elevator_lobby_alpha or state.current_loc == .elevator_lobby_beta) {
            if (!state.elevator_arrived) { jsPrint("The elevator is not here.\n"); return; }
            jsPrint("You step into the elevator.\n"); changeLocation(.elevator_interior);
        } else jsPrint("There is nothing to enter here.\n");
    } else if (std.mem.eql(u8, cmd, "push") or std.mem.eql(u8, cmd, "press")) {
        if (state.current_loc == .elevator_interior and !state.elevator_moving_down) {
            playSound(assets.elevator_button.ptr, assets.elevator_button.len, false);
            state.elevator_moving_down = true;
            jsPrint("The doors slide shut. The elevator begins to descend.\n"); triggerSpecialSequence(2);
        } else jsPrint("Nothing to push here.\n");
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
    } else if (std.mem.eql(u8, cmd, "go") or std.mem.eql(u8, cmd, "n") or std.mem.eql(u8, cmd, "s") or std.mem.eql(u8, cmd, "e") or std.mem.eql(u8, cmd, "w") or std.mem.eql(u8, cmd, "u") or std.mem.eql(u8, cmd, "d")) {
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
            if (loc == .main_reactor and state.hasItem(.power_board_c)) {
                state.setItem(.power_board_c, false); state.reactor_powered = true;
                playSound(assets.reactor_ignition_roar.ptr, assets.reactor_ignition_roar.len, false);
                jsPrint("The reactor roars with power! Main Generator is now ONLINE.\n"); handled = true;
            } else if (loc == .launch_control and state.hasItem(.control_board_b)) {
                if (!state.reactor_powered) jsPrint("The computer remains dark. It needs power from the Main Reactor.\n")
                else { state.setItem(.control_board_b, false); state.launch_computer_active = true;
                    playSound(assets.comms_uplink_chirp.ptr, assets.comms_uplink_chirp.len, false);
                    jsPrint("The launch computer flickers to life! Systems are now READY.\n"); }
                handled = true;
            } else if (loc == .escape_pod and state.hasItem(.interface_board_d)) {
                if (!state.launch_computer_active) jsPrint("The pod interface won't accept the board. The Launch Computer must be online.\n")
                else { state.setItem(.interface_board_d, false); state.pod_interface_ready = true;
                    playSound(assets.pod_systems_active.ptr, assets.pod_systems_active.len, false);
                    jsPrint("Pod systems synced with Launch Control. Interface Board D installed.\n"); }
                handled = true;
            }
        }
        if (!handled and (std.mem.eql(u8, target, "battery") or std.mem.eql(u8, target, ""))) {
            if (loc == .escape_pod) {
                if (!state.launch_computer_active) jsPrint("The battery slots are locked until the Launch Computer is powered.\n")
                else {
                    const batteries = [_]Item{ .battery_1, .battery_2, .battery_3, .battery_4 };
                    for (batteries) |b| {
                        if (state.hasItem(b)) {
                            state.setItem(b, false); state.batteries_inserted += 1;
                            playSound(assets.battery_insert.ptr, assets.battery_insert.len, false);
                            jsPrint("Battery installed. Total: ");
                            const count_str = [_]u8{ @as(u8, @intCast(state.batteries_inserted)) + '0' };
                            jsPrint(&count_str); jsPrint("/4\n"); handled = true; break;
                        }
                    }
                }
            }
        }
        if (!handled) jsPrint("Nothing to install here or you're missing the required part.\n");
        if (state.pod_interface_ready and state.batteries_inserted == 4) {
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