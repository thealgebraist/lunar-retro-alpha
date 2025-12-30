
def create_frame(mouth_open=0, zoom=0):
    # 32x32 grid
    grid = [[0 for _ in range(32)] for _ in range(32)]
    
    # Color map
    C_BLACK = 0
    C_RED = 1
    C_GREEN = 2
    C_YELLOW = 3
    C_GREY = 8
    C_WHITE = 7
    
    offset_x = 0
    offset_y = 0
    scale = 1.0
    
    if zoom > 0:
        scale = 1.2
        offset_x = -3
        offset_y = -3

    for y in range(32):
        for x in range(32):
            # Transform for zoom
            tx = int((x - 16) / scale + 16 - offset_x)
            ty = int((y - 16) / scale + 16 - offset_y)
            
            if 0 <= tx < 32 and 0 <= ty < 32:
                # Base head (Green)
                if 5 <= tx <= 26 and 4 <= ty <= 28:
                    grid[y][x] = C_GREEN
                
                # Hair (Black flat top)
                if 5 <= tx <= 26 and 2 <= ty <= 6:
                    grid[y][x] = C_BLACK
                
                # Eyes (Sunken, Red/Yellow)
                if ty == 10:
                    if 10 <= tx <= 13: grid[y][x] = C_BLACK # Socket
                    if 18 <= tx <= 21: grid[y][x] = C_BLACK # Socket
                if ty == 11:
                    if 10 <= tx <= 13: grid[y][x] = C_BLACK
                    if 11 <= tx <= 12: grid[y][x] = C_RED # Pupil
                    
                    if 18 <= tx <= 21: grid[y][x] = C_BLACK
                    if 19 <= tx <= 20: grid[y][x] = C_RED # Pupil

                # Nose
                if 14 <= tx <= 17 and 14 <= ty <= 17:
                    grid[y][x] = C_GREEN
                    if ty > 15: grid[y][x] = C_BLACK # Nostrils shadowing

                # Mouth
                mouth_y = 22
                mouth_h = 1 + mouth_open
                if mouth_y <= ty < mouth_y + mouth_h and 10 <= tx <= 21:
                    grid[y][x] = C_BLACK # Open mouth
                    # Teeth
                    if (ty == mouth_y or ty == mouth_y + mouth_h - 1) and tx % 2 == 0:
                         grid[y][x] = C_WHITE

                # Bolts (Grey)
                if ty >= 18 and ty <= 20:
                    if tx < 5 or tx > 26:
                         grid[y][x] = C_GREY

                # Scars
                if ty == 7 and 10 <= tx <= 20: grid[y][x] = C_BLACK # Forehead scar

    return grid

frames = []
frames.append(create_frame(mouth_open=0, zoom=0)) # Staring
frames.append(create_frame(mouth_open=2, zoom=0)) # Opening
frames.append(create_frame(mouth_open=5, zoom=0)) # Roaring
frames.append(create_frame(mouth_open=6, zoom=1)) # Lunging

import json
print(json.dumps(frames))
