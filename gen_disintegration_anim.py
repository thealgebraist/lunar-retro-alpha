import json
import random

def create_frame(light_on=True, disintegrate_level=0, stars=[]):
    # 32x32 grid
    grid = [[0 for _ in range(32)] for _ in range(32)]
    
    # Colors
    C_BLACK = 0
    C_WHITE = 7
    C_GREY = 8
    C_CYAN = 6 # Base metal
    C_YELLOW = 3 # Lights
    
    # Draw Stars
    for sx, sy in stars:
        grid[sy][sx] = C_WHITE

    # Draw simple base from distance
    center_x, center_y = 16, 16
    radius = 6
    
    if disintegrate_level < 10:
        for y in range(32):
            for x in range(32):
                dist = ((x - center_x)**2 + (y - center_y)**2)**0.5
                if dist <= radius:
                    # Flickering/disintegrating logic
                    if disintegrate_level > 0 and random.random() < (disintegrate_level / 10.0):
                        grid[y][x] = C_BLACK
                    else:
                        grid[y][x] = C_CYAN
                        # Small lights inside
                        if (x % 3 == 0 and y % 3 == 0):
                            grid[y][x] = C_YELLOW if light_on else C_BLACK

    return grid

# Pre-generate stars for consistency
random.seed(42)
stars = [(random.randint(0, 31), random.randint(0, 31)) for _ in range(20)]

frames = []
# 1-4: Flickering
frames.append(create_frame(light_on=True, disintegrate_level=0, stars=stars))
frames.append(create_frame(light_on=False, disintegrate_level=0, stars=stars))
frames.append(create_frame(light_on=True, disintegrate_level=1, stars=stars))
frames.append(create_frame(light_on=False, disintegrate_level=2, stars=stars))

# 5-9: Disintegrating
for i in range(3, 8):
    frames.append(create_frame(light_on=False, disintegrate_level=i, stars=stars))

# Last frame: Empty space with stars
frames.append(create_frame(light_on=False, disintegrate_level=10, stars=stars))

print(json.dumps(frames))