import pandas as pd

# 1️⃣ 원본 파일 경로 (공백 구분)
input_path = "german.data-numeric"   # 혹은 전체 경로 지정 가능

# 2️⃣ 출력 파일 이름
output_path = "german_numeric.csv"

# 3️⃣ 공백/탭으로 구분된 파일 읽기
df = pd.read_csv(input_path, header=None, delim_whitespace=True)

# 4️⃣ 쉼표(,) 구분 CSV로 저장
df.to_csv(output_path, header=False, index=False)

print(f"✅ Saved as '{output_path}' — shape: {df.shape}")