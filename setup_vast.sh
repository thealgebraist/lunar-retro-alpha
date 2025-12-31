#!/bin/bash
pip install diffusers transformers accelerate soundfile pydub scipy numpy opencv-python google-genai runwayml sentencepiece protobuf librosa
apt-get update && apt-get install -y libsndfile1 ffmpeg libgl1
