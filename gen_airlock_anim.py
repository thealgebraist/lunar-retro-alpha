import json

# 32x32 grid
# Colors: 0=Black, 8=Grey, 7=White(Stars), 4=Blue(Earth), 1=Red(Player?)

def create_blank():
    return [[0 for _ in range(32)] for _ in range(32)]

frames = []

# Frame 0: Closed Door
f0 = create_blank()
for y in range(5, 27):
    for x in range(10, 22):
        f0[y][x] = 8 # Grey Door
# Door seam
for y in range(5, 27):
    f0[y][15] = 0
    f0[y][16] = 0
frames.append(f0)

# Frame 1: Door opening slightly
f1 = create_blank()
for y in range(5, 27):
    for x in range(8, 14): f1[y][x] = 8
    for x in range(18, 24): f1[y][x] = 8
    # Reveal space (stars)
    f1[y][15] = 7 if y%5==0 else 0
    f1[y][16] = 7 if y%7==0 else 0
frames.append(f1)

# Frame 2: Door wider
f2 = create_blank()
for y in range(5, 27):
    for x in range(6, 10): f2[y][x] = 8
    for x in range(22, 26): f2[y][x] = 8
    # More space
    for x in range(10, 22):
        if (x+y)%7 == 0: f2[y][x] = 7
frames.append(f2)

# Frame 3: Wide open, Vacuum rush visual (lines)
f3 = create_blank()
for y in range(5, 27):
    for x in range(4, 8): f3[y][x] = 8
    for x in range(24, 28): f3[y][x] = 8
    # Suck lines
    for x in range(8, 24):
        if y%2==0: f3[y][x] = 7 # White streaks
frames.append(f3)

# Frame 4: Player appears (red dot) being pulled
f4 = create_blank()
for y in range(5, 27):
    for x in range(4, 8): f4[y][x] = 8
    for x in range(24, 28): f4[y][x] = 8
    if y%2==0: f4[y][range(8,24)[(y+1)%16]] = 7
# Player at bottom
f4[25][16] = 1 
f4[24][16] = 1
f4[25][15] = 1
frames.append(f4)

# Frame 5: Player moving up/out
f5 = create_blank()
for y in range(5, 27):
    for x in range(4, 8): f5[y][x] = 8
    for x in range(24, 28): f5[y][x] = 8
# Player mid air
f5[18][16] = 1 
f5[17][16] = 1
f5[18][15] = 1
# Debris
f5[20][12] = 8
f5[22][20] = 8
frames.append(f5)

# Frame 6: Player smaller, further out
f6 = create_blank()
for y in range(5, 27):
    for x in range(4, 8): f6[y][x] = 8
    for x in range(24, 28): f6[y][x] = 8
# Player small
f6[12][16] = 1 
frames.append(f6)

# Frame 7: Gone. Just stars.
f7 = create_blank()
for y in range(5, 27):
    for x in range(4, 8): f7[y][x] = 8
    for x in range(24, 28): f7[y][x] = 8
    for x in range(8, 24):
        if (x*y)%13 == 0: f7[y][x] = 7
frames.append(f7)

print(json.dumps(frames))
