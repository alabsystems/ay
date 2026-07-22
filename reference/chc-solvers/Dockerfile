FROM ubuntu:22.04
RUN apt-get update && apt-get install -y wget unzip default-jre && rm -rf /var/lib/apt/lists/*

# LoAT
RUN wget -q https://github.com/LoAT-developers/LoAT/releases/download/v0.9.5/loat-static -O /usr/local/bin/loat && chmod +x /usr/local/bin/loat

# UltimateTreeAutomizer  
RUN cd /opt && wget -q https://github.com/ultimate-pa/ultimate/releases/download/v0.3.1/UltimateAutomizer-linux.zip && unzip -q UltimateAutomizer-linux.zip && rm UltimateAutomizer-linux.zip

WORKDIR /benchmarks
