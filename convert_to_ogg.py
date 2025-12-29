import os
import subprocess

def convert_wav_to_ogg(wav_path):
    ogg_path = wav_path.replace('.wav', '.ogg')
    print(f"Converting {wav_path} to {ogg_path}...")
    ffmpeg_bin = os.environ.get('FFMPEG', 'ffmpeg')
    # -q:a 6 is high quality (approx 192kbps)
    cmd = [ffmpeg_bin, '-y', '-i', wav_path, '-c:a', 'libvorbis', '-q:a', '6', ogg_path]
    subprocess.run(cmd, stdout=subprocess.DEVNULL, stderr=subprocess.DEVNULL)

def main():
    asset_dir = "moon_base_assets"
    files = [f for f in os.listdir(asset_dir) if f.endswith(".wav")]
    for f in files:
        convert_wav_to_ogg(os.path.join(asset_dir, f))
    print("Conversion complete.")

if __name__ == "__main__":
    main()
