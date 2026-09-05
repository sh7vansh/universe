import numpy as np

S = np.load('optimal_S_matrix.npy')
primes = [2, 3, 5, 7, 11, 13, 17, 19, 23, 29]

md = '# The Tuned Scattering Matrix (S)\n\n'
md += 'This 10x10 unitary matrix forces the graph to ring at the Riemann zeros. '
md += 'Values are presented as `Magnitude ∠ Phase` (phase in pi radians).\n\n'
md += 'Rows represent the incoming wave from a prime loop, and columns represent the outgoing wave.\n\n'

md += '| Prime | ' + ' | '.join([str(p) for p in primes]) + ' |\n'
md += '|---|' + '|'.join(['---'] * 10) + '|\n'

for i in range(10):
    row = f'| **{primes[i]}** | '
    cells = []
    for j in range(10):
        mag = np.abs(S[i,j])
        phase = np.angle(S[i,j])/np.pi
        cells.append(f'{mag:.3f} ∠ {phase:.2f}')
    row += ' | '.join(cells) + ' |\n'
    md += row

output_file = '/home/shivansh/.gemini/antigravity-cli/brain/c1b40e65-9f7d-40c3-9080-8eb8bc2b974b/tuned_scattering_matrix.md'
with open(output_file, 'w') as f:
    f.write(md)
    
print("Artifact generated.")
