import os

# 1. Get the latest base64 data
with open('game.wasm.base64', 'r') as f:
    b64_data = f.read().strip()

# 2. Get the animation frames
with open('backstory_frames.json', 'r') as f:
    frames_data = f.read().strip()

# 3. Read the template
with open('index.template.html', 'r') as f:
    content = f.read()

# 4. Replace WASM
start_marker = 'const WASM_BASE64 = "'
end_marker = '";'
start_idx = content.find(start_marker)
end_idx = content.find(end_marker, start_idx + len(start_marker))
content = content[:start_idx + len(start_marker)] + b64_data + content[end_idx:]

# 5. Replace Animation Data (I need to add this marker to the template first)
anim_marker = 'const ANIMATION_DATA = '
anim_end = ';'
a_start = content.find(anim_marker)
a_end = content.find(anim_end, a_start + len(anim_marker))
if a_start != -1:
    content = content[:a_start + len(anim_marker)] + frames_data + content[a_end:]

# 6. Write to index.html and template
with open('index.html', 'w') as f:
    f.write(content)
with open('index.template.html', 'w') as f:
    f.write(content)

print(f"Successfully embedded WASM and Animation into index.html")
