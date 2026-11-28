# Decides the four 87-byte equality files (w = 16; signs in words 34 and 39) in 4 stored instructions.
x = load 34
y = load 39
z = mul x y
br ltu z 35779 NO YES
