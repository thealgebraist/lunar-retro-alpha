import os
import numpy as np
import scipy.io.wavfile

def normalize_audio(file_path, target_rms_db=-18.0):
    sample_rate, data = scipy.io.wavfile.read(file_path)
    
    # Convert to float
    orig_dtype = data.dtype
    if data.dtype == np.int16:
        data_float = data.astype(np.float32) / 32768.0
    else:
        data_float = data.astype(np.float32) # Assume float or handle others
        
    # Calculate current RMS
    rms = np.sqrt(np.mean(data_float**2))
    
    if rms == 0:
        return # Skip silent files
        
    # Calculate gain
    target_rms = 10**(target_rms_db / 20)
    gain = target_rms / rms
    
    # Apply gain
    normalized = data_float * gain
    
    # Check for clipping and limit if necessary
    peak = np.max(np.abs(normalized))
    if peak > 0.99:
        normalized = normalized * (0.99 / peak)
        
    # Convert back to original dtype
    if orig_dtype == np.int16:
        final_data = (normalized * 32767).astype(np.int16)
    else:
        final_data = normalized.astype(orig_dtype)
        
    scipy.io.wavfile.write(file_path, sample_rate, final_data)

def main():
    asset_dir = "moon_base_assets"
    files = [f for f in os.listdir(asset_dir) if f.endswith(".wav")]
    
    print(f"Normalizing {len(files)} files to -18dB RMS...")
    for f in files:
        path = os.path.join(asset_dir, f)
        # We don't want to normalize escape_pod if it's meant to be silent
        if f == "escape_pod.wav":
            continue
        normalize_audio(path)
    print("Normalization complete.")

if __name__ == "__main__":
    main()
