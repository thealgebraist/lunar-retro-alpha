import os
import numpy as np
import scipy.io.wavfile

def make_loopable(file_path, crossfade_duration_s=2.0):
    sample_rate, data = scipy.io.wavfile.read(file_path)
    
    # Convert to float
    orig_dtype = data.dtype
    if data.dtype == np.int16:
        data_float = data.astype(np.float32) / 32768.0
    else:
        data_float = data.astype(np.float32)

    num_samples = len(data_float)
    fade_samples = int(crossfade_duration_s * sample_rate)
    
    if num_samples <= fade_samples * 2:
        print(f"Skipping {file_path}: too short for {crossfade_duration_s}s crossfade")
        return

    # Extract the parts
    # We'll take the last fade_samples and blend them with the first fade_samples
    start_fade = data_float[:fade_samples]
    end_fade = data_float[-fade_samples:]
    middle = data_float[fade_samples:-fade_samples]
    
    # Create crossfade weights
    alpha = np.linspace(0, 1, fade_samples)
    
    # Blended part: end fades out (1->0), start fades in (0->1)
    # Actually, to make it loop: 
    # The new start of the file will be (end_fade * (1-alpha) + start_fade * alpha)
    # And we'll remove the end_fade from the end.
    
    blended = end_fade * (1 - alpha) + start_fade * alpha
    
    # New audio is [blended, middle]
    loopable = np.concatenate([blended, middle])
    
    # Convert back to original dtype
    if orig_dtype == np.int16:
        final_data = (loopable * 32767).astype(np.int16)
    else:
        final_data = loopable.astype(orig_dtype)
        
    scipy.io.wavfile.write(file_path, sample_rate, final_data)
    print(f"Made {file_path} loopable (new length: {len(loopable)/sample_rate:.2f}s)")

def main():
    asset_dir = "moon_base_assets"
    # Only location sounds are 10 seconds long
    locations = [
        "observation_dome.wav", "comms_array.wav", "security_hub.wav", 
        "elevator_lobby_alpha.wav", "mess_hall.wav", "sleeping_pods.wav", 
        "medical_lab.wav", "elevator_lobby_beta.wav", "main_reactor.wav", 
        "fuel_storage.wav", "battery_bank.wav", "maintenance_tunnels.wav", 
        "cargo_loading.wav", "oxygen_scrubbers.wav", "launch_control.wav", 
        "escape_pod.wav"
    ]
    
    print("Processing background sounds for seamless looping...")
    for f in locations:
        path = os.path.join(asset_dir, f)
        if os.path.exists(path):
            make_loopable(path)
    print("Looping processing complete.")

if __name__ == "__main__":
    main()
