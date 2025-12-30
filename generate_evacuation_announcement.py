# Reprocess the audio more conservatively to avoid artifacts/noise.

from pydub import AudioSegment, effects
from pydub.generators import WhiteNoise

src = "/mnt/data/evacuate_announcement.ogg"
audio = AudioSegment.from_file(src)

# Mono PA
audio = audio.set_channels(1)

# Band-limit (small PA feel)
audio = audio.high_pass_filter(220)
audio = audio.low_pass_filter(5200)

# Gentle saturation (much lighter than before)
audio = audio.apply_gain(+2)
audio = effects.compress_dynamic_range(audio, threshold=-20, ratio=2.0)

# Distance cue: soften highs a bit more
audio = audio.low_pass_filter(4200)

# Early reflections (very subtle)
early = (audio - 10)
audio = audio.overlay(early, position=55)
audio = audio.overlay(early - 3, position=165)

# “Underground” tail via layered quiet delays (short + long)
def bunker_tail(seg):
    out = seg
    taps = [
        (140, 16),
        (310, 18),
        (620, 20),
        (1050, 22),
        (1650, 24),
    ]
    for d,g in taps:
        out = out.overlay(seg - g, position=d)
    return out

audio = bunker_tail(audio)

# Slight ambience bed
noise = WhiteNoise().to_audio_segment(duration=len(audio)).low_pass_filter(900) - 48
audio = audio.overlay(noise)

# Normalize gently
audio = effects.normalize(audio - 1)

out = "/mnt/data/evac_sci_fi_processed_v2.ogg"
audio.export(out, format="ogg")

out
