import json

def get_empty_frame():
    return [[0 for _ in range(32)] for _ in range(32)]

frames = []

# --- 1-4: Thriving Base ---
for i in range(4):
    f = get_empty_frame()
    # Earth
    for y in range(5, 12):
        for x in range(20, 27):
            if (x-23.5)**2 + (y-8.5)**2 < 12: f[y][x] = 4 # Blue
    # Moon Surface
    for y in range(25, 32):
        for x in range(32): f[y][x] = 7 # White/Grey
    # Domes
    for x in range(5, 15):
        for y in range(20, 25):
            if (x-10)**2 + (y-25)**2 < 25: f[y][x] = 6 # Cyan glass
    # Lights
    if i % 2 == 0:
        f[22][10] = 3
        f[23][7] = 3
    frames.append(f)

# --- 5-8: Impact ---
for i in range(4):
    f = get_empty_frame()
    # Earth & Moon same
    for y in range(5, 12):
        for x in range(20, 27):
            if (x-23.5)**2 + (y-8.5)**2 < 12: f[y][x] = 4
    for y in range(25, 32):
        for x in range(32): f[y][x] = 7
    # Meteor
    mx, my = 30 - i*5, 5 + i*4
    f[my][mx] = 1 # Red
    f[my-1][mx+1] = 3 # Trail
    # Domes
    for x in range(5, 15):
        for y in range(20, 25):
            if (x-10)**2 + (y-25)**2 < 25: f[y][x] = 6
    if i == 3: # Impact frame
        for y in range(18, 28):
            for x in range(8, 18):
                if (x-13)**2 + (y-23)**2 < 16: f[y][x] = 3 # Yellow flash
    frames.append(f)

# --- 9-12: Destruction ---
for i in range(4):
    f = get_empty_frame()
    for y in range(25, 32):
        for x in range(32): f[y][x] = 7
    # Fire
    for _ in range(20):
        import random
        rx, ry = 10 + random.randint(-5, 5), 23 + random.randint(-3, 3)
        if 0<=rx<32 and 0<=ry<32: f[ry][rx] = 1 if i%2==0 else 3
    # Broken domes
    for x in range(5, 15):
        for y in range(20, 25):
            if (x-10)**2 + (y-25)**2 < 25 and random.random() > 0.4: f[y][x] = 0 # Holes
    frames.append(f)

# --- 13-16: Leaving ---
for i in range(4):
    f = get_empty_frame()
    for y in range(25, 32):
        for x in range(32): f[y][x] = 7
    # Ruined Base
    for x in range(5, 15):
        for y in range(22, 25): f[y][x] = 0
    # Rocket leaving
    rx, ry = 15 + i*2, 20 - i*4
    if 0<=rx<32 and 0<=ry<32:
        f[ry][rx] = 7
        f[ry+1][rx] = 1 # Flame
    frames.append(f)

print(json.dumps(frames))
