import os
import numpy as np
import scipy.io.wavfile

def get_loudness(file_path):
    sample_rate, data = scipy.io.wavfile.read(file_path)
    
    # Convert to float in range [-1, 1]
    if data.dtype == np.int16:
        data = data.astype(np.float32) / 32768.0
    elif data.dtype == np.int32:
        data = data.astype(np.float32) / 2147483648.0
    elif data.dtype == np.uint8:
        data = (data.astype(np.float32) - 128.0) / 128.0
        
    # Peak amplitude
    peak = np.max(np.abs(data))
    peak_db = 20 * np.log10(peak) if peak > 0 else -100
    
    # RMS amplitude
    rms = np.sqrt(np.mean(data**2))
    rms_db = 20 * np.log10(rms) if rms > 0 else -100
    
    return peak_db, rms_db

def main():
    asset_dir = "moon_base_assets"
    files = sorted([f for f in os.listdir(asset_dir) if f.endswith(".wav")])
    
    print(f"{'File Name':<30} | {'Peak dB':<10} | {'RMS dB':<10}")
    print("-" * 56)
    
    for f in files:
        path = os.path.join(asset_dir, f)
        peak, rms = get_loudness(path)
        print(f"{f:<30} | {peak:7.2f} dB | {rms:7.2f} dB")

if __name__ == "__main__":
    main()
