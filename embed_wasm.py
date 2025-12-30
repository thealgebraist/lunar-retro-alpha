import os

# 1. Get the latest base64 data
with open('game.wasm.base64', 'r') as f:
    b64_data = f.read().strip()

# 2. Get the animation frames
with open('backstory_frames.json', 'r') as f:
    frames_data = f.read().strip()

with open('airlock_frames.json', 'r') as f:
    airlock_data = f.read().strip()

with open('alien_frames.json', 'r') as f:
    alien_data = f.read().strip()

with open('disintegration_frames.json', 'r') as f:
    disintegration_data = f.read().strip()

# 3. Read the template
with open('index.template.html', 'r') as f:
    content = f.read()

# 4. Replace WASM
start_marker = 'const WASM_BASE64 = "'
end_marker = '";'
start_idx = content.find(start_marker)
end_idx = content.find(end_marker, start_idx + len(start_marker))
content = content[:start_idx + len(start_marker)] + b64_data + content[end_idx:]

# 5. Replace Animation Data
anim_marker = 'const ANIMATION_DATA = '
anim_end = ';'
a_start = content.find(anim_marker)
a_end = content.find(anim_end, a_start + len(anim_marker))
if a_start != -1:
    content = content[:a_start + len(anim_marker)] + frames_data + content[a_end:]

# 6. Replace Airlock Animation Data
air_marker = 'const AIRLOCK_ANIMATION_DATA = '
air_end = ';'
air_start = content.find(air_marker)
air_end_idx = content.find(air_end, air_start + len(air_marker))
if air_start != -1:
    content = content[:air_start + len(air_marker)] + airlock_data + content[air_end_idx:]

# 7. Replace Alien Animation Data
alien_marker = 'const ALIEN_ANIMATION_DATA = '
alien_end = ';'
alien_start = content.find(alien_marker)
alien_end_idx = content.find(alien_end, alien_start + len(alien_marker))
if alien_start != -1:
    content = content[:alien_start + len(alien_marker)] + alien_data + content[alien_end_idx:]

# 8. Replace Disintegration Animation Data
dis_marker = 'const DISINTEGRATION_ANIMATION_DATA = '
dis_end = ';'
dis_start = content.find(dis_marker)
dis_end_idx = content.find(dis_end, dis_start + len(dis_marker))
if dis_start != -1:
    content = content[:dis_start + len(dis_marker)] + disintegration_data + content[dis_end_idx:]

# 9. Write to index.html and template
with open('index.html', 'w') as f:
    f.write(content)
with open('index.template.html', 'w') as f:
    f.write(content)

print(f"Successfully embedded WASM and Animation into index.html")
