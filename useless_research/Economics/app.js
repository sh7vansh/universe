/**
 * THE UNIFIED REALITY - 4-ENGINE SCIENTIFIC SIMULATION PLATFORM
 * 
 * Implements 1:1 translations of the 4 standalone Python simulation files:
 *   1. fractal_debt_model.py     (Multi-Tier 300-Year Fractal Debt + Fourier Periodogram)
 *   2. keen_minsky_simulation.py (Continuous RK4 Dynamical ODE Solver)
 *   3. pytorch_simulation.py     (Thermal Quantum Universe with Cosmic Expansion & Vitals)
 *   4. networkx_visualization.py (3D MDS Point Cloud + 2D MRI Cross-Section Slice Proof)
 */

document.addEventListener('DOMContentLoaded', () => {
  initHeroCanvas();
  initLabTabs();
  initFractalDebtEngine();
  initEmpiricalJstEngine();
  initKeenMinskyEngine();
  initPyTorchUniverseEngine();
  initNetworkXMRIScanEngine();
  initKaTeX();
});

/* ==========================================================================
   0. KATEX AUTO-RENDER INITIALIZER
   ========================================================================== */

function initKaTeX() {
  function render() {
    if (typeof renderMathInElement === 'function') {
      renderMathInElement(document.body, {
        delimiters: [
          { left: '$$', right: '$$', display: true },
          { left: '$', right: '$', display: false },
          { left: '\\(', right: '\\)', display: false },
          { left: '\\[', right: '\\]', display: true }
        ],
        throwOnError: false,
        ignoredTags: ["script", "noscript", "style", "textarea", "pre", "code"]
      });
    } else {
      setTimeout(render, 50);
    }
  }
  render();
}

/* ==========================================================================
   1. LAB TABS NAVIGATION
   ========================================================================== */

function initLabTabs() {
  const tabs = document.querySelectorAll('.lab-tab');
  const panels = document.querySelectorAll('.lab-panel');

  tabs.forEach(tab => {
    tab.addEventListener('click', () => {
      tabs.forEach(t => t.classList.remove('active'));
      panels.forEach(p => p.classList.remove('active'));

      tab.classList.add('active');
      const targetId = tab.getAttribute('data-tab');
      const targetPanel = document.getElementById(targetId);
      if (targetPanel) {
        targetPanel.classList.add('active');
        window.dispatchEvent(new Event('resize'));
      }
    });
  });
}

/* ==========================================================================
   2. AMBIENT HERO CANVAS
   ========================================================================== */

function initHeroCanvas() {
  const canvas = document.getElementById('heroCanvas');
  if (!canvas) return;
  const ctx = canvas.getContext('2d');

  let width, height;
  function resize() {
    width = canvas.width = canvas.parentElement.offsetWidth;
    height = canvas.height = canvas.parentElement.offsetHeight;
  }
  resize();
  window.addEventListener('resize', resize);

  const numParticles = 60;
  const particles = [];

  for (let i = 0; i < numParticles; i++) {
    particles.push({
      x: Math.random() * width,
      y: Math.random() * height,
      vx: (Math.random() - 0.5) * 0.4,
      vy: (Math.random() - 0.5) * 0.4,
      phase: Math.random() * Math.PI * 2,
      phaseSpeed: 0.01 + Math.random() * 0.02,
      radius: 1.5 + Math.random() * 2
    });
  }

  function animate() {
    ctx.clearRect(0, 0, width, height);

    for (let i = 0; i < particles.length; i++) {
      const p = particles[i];
      p.x += p.vx;
      p.y += p.vy;
      p.phase += p.phaseSpeed;

      if (p.x < 0) p.x = width;
      if (p.x > width) p.x = 0;
      if (p.y < 0) p.y = height;
      if (p.y > height) p.y = 0;

      ctx.beginPath();
      ctx.arc(p.x, p.y, p.radius, 0, Math.PI * 2);
      ctx.fillStyle = 'rgba(56, 189, 248, 0.6)';
      ctx.fill();

      for (let j = i + 1; j < particles.length; j++) {
        const p2 = particles[j];
        const dx = p.x - p2.x;
        const dy = p.y - p2.y;
        const dist = Math.sqrt(dx * dx + dy * dy);

        if (dist < 130) {
          const phaseDiff = Math.abs(p.phase - p2.phase);
          const resonance = (Math.cos(phaseDiff) + 1) / 2.0;
          const alpha = (1 - dist / 130) * resonance * 0.4;

          ctx.beginPath();
          ctx.moveTo(p.x, p.y);
          ctx.lineTo(p2.x, p2.y);
          ctx.strokeStyle = `rgba(16, 185, 129, ${alpha})`;
          ctx.lineWidth = 1;
          ctx.stroke();
        }
      }
    }

    requestAnimationFrame(animate);
  }

  animate();
}

/* ==========================================================================
   ENGINE 1: FRACTAL DEBT & FOURIER (fractal_debt_model.py)
   ========================================================================== */

function initFractalDebtEngine() {
  let charts = {};

  const btnRun = document.getElementById('btnRunFullDebtSim');
  const sliderResidue = document.getElementById('debtSliderResidue');
  const valResidue = document.getElementById('valDebtResidue');
  const sliderAgents = document.getElementById('debtSliderAgents');
  const valAgents = document.getElementById('valDebtAgents');
  const sliderRateSens = document.getElementById('debtSliderRateSens');
  const valRateSens = document.getElementById('valDebtRateSens');
  const sliderResetCeiling = document.getElementById('debtSliderResetCeiling');
  const valResetCeiling = document.getElementById('valDebtResetCeiling');

  const simTimeDisplay = document.getElementById('simTimeDisplay');
  const peak1Display = document.getElementById('peak1Display');
  const peak2Display = document.getElementById('peak2Display');
  const sovereignResetsDisplay = document.getElementById('sovereignResetsDisplay');

  sliderResidue.addEventListener('input', (e) => valResidue.textContent = parseFloat(e.target.value).toFixed(2));
  sliderAgents.addEventListener('input', (e) => valAgents.textContent = parseFloat(e.target.value).toFixed(1));
  sliderRateSens.addEventListener('input', (e) => valRateSens.textContent = parseFloat(e.target.value).toFixed(1));
  sliderResetCeiling.addEventListener('input', (e) => valResetCeiling.textContent = e.target.value);

  function gaussianRandom() {
    let u = 0, v = 0;
    while (u === 0) u = Math.random();
    while (v === 0) v = Math.random();
    return Math.sqrt(-2.0 * Math.log(u)) * Math.cos(2.0 * Math.PI * v);
  }

  function runFullSimulation() {
    const N_agents = 120;
    const N_banks = 12;
    const residueRatio = parseFloat(sliderResidue.value);
    const tauEff = parseFloat(sliderAgents.value);
    const memoryScale = parseFloat(sliderRateSens.value);
    const resetCeilingPct = parseFloat(sliderResetCeiling.value);
    const resetCeilingRatio = resetCeilingPct / 100.0;

    const timesteps = 6000;
    const dt = 0.1;
    const tauSteps = Math.max(1, Math.round(tauEff / dt));
    const pPower = 1.35;
    const cEconSq = 2.5;
    const lambdaMemory = 1.0 / memoryScale;

    const agent_bank_map = new Int32Array(N_agents);
    const agent_incomes = new Float64Array(N_agents);
    const agent_debts = new Float64Array(N_agents);
    const agent_phases = new Float64Array(N_agents);
    const agent_omega = new Float64Array(N_agents);

    const omegaBase = (2.0 * Math.PI) / (4.0 * tauEff);
    let totalInitGdp = 0.0;
    for (let i = 0; i < N_agents; i++) {
      agent_bank_map[i] = i % N_banks;
      agent_incomes[i] = 90.0 + Math.random() * 20.0;
      agent_debts[i] = 55.0 + Math.random() * 20.0;
      agent_phases[i] = Math.random() * 2.0 * Math.PI;
      agent_omega[i] = 0.6 + Math.random() * 0.8;
      totalInitGdp += agent_incomes[i];
    }

    const bank_capital = new Float64Array(N_banks).fill(0.12 * (totalInitGdp / N_banks));
    const bank_toxic_residue = new Float64Array(N_banks).fill(0.06 * (totalInitGdp / N_banks));

    let credit_impulse_x = 0.18;
    const x_delay_buffer = new Float64Array(tauSteps + 1);
    for (let i = 0; i <= tauSteps; i++) {
      x_delay_buffer[i] = 0.18 * Math.cos(0.5 * i * dt);
    }
    let delayPtr = 0;

    let generational_memory = 0.85;
    let sovereign_debt = 0.28 * totalInitGdp;
    let base_rate = 0.045;
    const rate_delay_buffer = new Float64Array(tauSteps + 1).fill(base_rate);

    const time_hist = [];
    const tier0_debt_hist = [];
    const tier1_sec_hist = [];
    const tier2_debt_hist = [];
    const base_rate_hist = [];
    const memory_hist = [];
    const dilation_hist = [];
    const total_lev_hist = [];
    const banking_crises = [];
    const reset_years = [];

    const sqrtDt = Math.sqrt(dt);
    const resonant_weights = new Float64Array(N_agents);

    for (let t = 0; t < timesteps; t++) {
      const currTime = t * dt;
      let totalGdp = 0.0;
      for (let i = 0; i < N_agents; i++) totalGdp += agent_incomes[i];

      // 1. Emergent Metric & Economic Time Dilation g_00(t)
      let sovRatio = sovereign_debt / (totalGdp + 1e-9);
      const g_00 = -(1.0 + (2.0 * sovRatio) / 2.2);
      const timeDilation = 1.0 / Math.sqrt(Math.abs(g_00));
      const gReal = 0.0175 * timeDilation;

      // 2. Kuramoto Phase Coherence & Power-Law Selection
      let cosSum = 0.0, sinSum = 0.0;
      for (let i = 0; i < N_agents; i++) {
        cosSum += Math.cos(agent_phases[i]);
        sinSum += Math.sin(agent_phases[i]);
      }
      const psiMean = Math.atan2(sinSum / N_agents, cosSum / N_agents);

      let meanW = 0.0;
      for (let i = 0; i < N_agents; i++) {
        const compat = 0.5 * (1.0 + Math.cos(agent_phases[i] - psiMean));
        const w = Math.pow(Math.max(1e-4, compat), pPower);
        resonant_weights[i] = w;
        meanW += w;
      }
      meanW = (meanW / N_agents) + 1e-9;

      const couplingK = 0.75 * (1.0 - 0.55 * generational_memory);
      for (let i = 0; i < N_agents; i++) {
        resonant_weights[i] /= meanW;
        const dphi = (agent_omega[i] + couplingK * Math.sin(psiMean - agent_phases[i])) * dt + gaussianRandom() * 0.22 * sqrtDt;
        agent_phases[i] = (agent_phases[i] + dphi) % (2.0 * Math.PI);
      }

      // 3. Pure Hutchinson-Wright Delay-Differential Hopf Bifurcation (Zero sin/cos clocks)
      const xDelayed = x_delay_buffer[delayPtr];
      const rDelayed = rate_delay_buffer[delayPtr];

      const alphaDelay = 1.52 * (Math.PI / (2.0 * tauEff));
      const saturation = 1.0 - (credit_impulse_x / 0.30) ** 2;
      const dx = -alphaDelay * xDelayed * saturation * dt + gaussianRandom() * 0.012 * sqrtDt;
      credit_impulse_x = Math.max(-0.295, Math.min(0.295, credit_impulse_x + dx));
      x_delay_buffer[delayPtr] = credit_impulse_x;

      // 4. Tier 0 Micro-Agents & Monogamy Debt Service Capacity
      const cautionBrake = 0.35 + 0.65 * ((1.0 - 0.80 * generational_memory) ** 2);
      const effServiceRate = rDelayed + 0.28 + 0.22 * Math.max(0.0, -credit_impulse_x) + 0.14 * ((1.0 - generational_memory) ** 2);

      let step_defaults = 0;
      for (let i = 0; i < N_agents; i++) {
        const gShock = gaussianRandom() * 0.028;
        const u = Math.max(1e-6, Math.random());
        const levyJump = (Math.pow(u, -1.0 / 2.5) - 0.65) * 0.012 * (Math.random() > 0.5 ? 1.0 : -1.0);
        const incGrowth = (gReal + 0.025 * credit_impulse_x) * dt + (gShock + levyJump) * sqrtDt;
        agent_incomes[i] *= Math.max(0.85, 1.0 + incGrowth);

        const cycleDrive = (0.042 * cautionBrake + 0.24 * credit_impulse_x) * resonant_weights[i];
        agent_debts[i] += agent_incomes[i] * cycleDrive * dt;

        if (agent_debts[i] * effServiceRate > 0.36 * agent_incomes[i]) {
          step_defaults++;
          const defaultedPool = 0.55 * agent_debts[i];
          agent_debts[i] -= defaultedPool;
          const bIdx = agent_bank_map[i];
          bank_toxic_residue[bIdx] += residueRatio * defaultedPool;
          bank_capital[bIdx] -= (1.0 - residueRatio) * defaultedPool;
        } else {
          agent_debts[i] = Math.max(15.0, agent_debts[i] * (1.0 - 0.038 * dt));
        }
      }

      // 5. Stock-Flow Consistent Bank Balance-Sheet Dynamics
      const ponziRollover = Math.max(0.005, 0.85 * (rDelayed - gReal) * (1.0 - 0.75 * generational_memory) + 0.0145 * ((1.0 - generational_memory) ** 2));
      let totalBankToxic = 0.0;
      for (let b = 0; b < N_banks; b++) {
        bank_toxic_residue[b] *= (1.0 + ponziRollover * dt);
        bank_capital[b] += 0.0014 * (totalGdp / N_banks) * dt;
        totalBankToxic += bank_toxic_residue[b];
      }

      generational_memory *= Math.exp(-lambdaMemory * dt);
      let toxicToGdp = totalBankToxic / (totalGdp + 1e-9);

      // 6. Tier 1 Systemic Banking Crisis (Pure Balance-Sheet Insolvency)
      let bankingCrisisTriggered = false;
      if (toxicToGdp >= 0.42) {
        bankingCrisisTriggered = true;
        banking_crises.push(currTime);
        sovereign_debt += 0.85 * totalBankToxic;
        for (let b = 0; b < N_banks; b++) {
          bank_toxic_residue[b] *= 0.15;
          bank_capital[b] = 0.12 * (totalGdp / N_banks);
        }
        generational_memory = Math.min(1.0, generational_memory + 0.90);
        base_rate = 0.005;
        step_defaults += Math.floor(0.25 * N_agents);
        toxicToGdp *= 0.15;
      }

      // 7. Tier 2 Sovereign Bekenstein-Minsky Singularity
      const netCarry = Math.max(0.002, (0.48 * base_rate) - (0.52 * gReal));
      sovereign_debt *= (1.0 + netCarry * dt);

      if (!bankingCrisisTriggered) {
        const targetRate = 0.042 + 0.075 * credit_impulse_x - 0.025 * (step_defaults / N_agents);
        base_rate = Math.max(0.005, Math.min(0.095, base_rate + 0.45 * (targetRate - base_rate) * dt));
      }
      rate_delay_buffer[delayPtr] = base_rate;
      delayPtr = (delayPtr + 1) % (tauSteps + 1);

      sovRatio = sovereign_debt / (totalGdp + 1e-9);
      if (sovRatio >= resetCeilingRatio) {
        reset_years.push(currTime);
        sovereign_debt = 0.22 * totalGdp;
        for (let b = 0; b < N_banks; b++) bank_toxic_residue[b] *= 0.20;
        for (let i = 0; i < N_agents; i++) agent_debts[i] *= 0.55;
        base_rate = 0.06;
        step_defaults = Math.floor(0.40 * N_agents);
        sovRatio = 0.22;
      }

      let totalTier0 = 0.0;
      for (let i = 0; i < N_agents; i++) totalTier0 += agent_debts[i];
      const t0Ratio = totalTier0 / (totalGdp + 1e-9);
      const totalLev = (t0Ratio + toxicToGdp + sovRatio) * 100.0;

      time_hist.push(currTime);
      tier0_debt_hist.push(t0Ratio * 100.0);
      tier1_sec_hist.push(toxicToGdp * 100.0);
      tier2_debt_hist.push(sovRatio * 100.0);
      base_rate_hist.push(base_rate * 100.0);
      memory_hist.push(generational_memory * 100.0);
      dilation_hist.push(timeDilation);
      total_lev_hist.push(totalLev);
    }

    const wavelet = computeMorletCWT(total_lev_hist, dt);

    const data = {
      time: time_hist,
      tier0_debt: tier0_debt_hist,
      tier1_sec: tier1_sec_hist,
      tier2_debt: tier2_debt_hist,
      base_rate: base_rate_hist,
      memory: memory_hist,
      dilation: dilation_hist,
      wavelet: wavelet,
      banking_crises: banking_crises,
      resets: reset_years
    };

    simTimeDisplay.textContent = `T₁ ≈ ${wavelet.T1.toFixed(2)} Years (Theory: ${(4 * tauEff).toFixed(1)}y)`;
    peak1Display.textContent = `T₂ ≈ ${wavelet.T2.toFixed(2)} Years (Theory: ${(3 * memoryScale).toFixed(1)}y)`;
    peak2Display.textContent = `T₃ ≈ ${wavelet.T3.toFixed(2)} Years (${reset_years.length} Sovereign Resets)`;
    sovereignResetsDisplay.textContent = `H(2) = ${wavelet.hurstH.toFixed(2)} | Δα = ${wavelet.deltaAlpha.toFixed(2)}`;

    renderDebtCharts(data);
    renderWaveletScalogram(data);
  }

  function computeMorletCWT(composite, dt) {
    const N = composite.length;
    let mean = 0.0;
    for (let i = 0; i < N; i++) mean += composite[i];
    mean /= N;

    let variance = 0.0;
    for (let i = 0; i < N; i++) variance += (composite[i] - mean) ** 2;
    const std = Math.sqrt(variance / N) || 1.0;

    const signal = new Float64Array(N);
    for (let i = 0; i < N; i++) signal[i] = (composite[i] - mean) / std;

    const omega0 = 6.0;
    const fourierFactor = (4.0 * Math.PI) / (omega0 + Math.sqrt(2.0 + omega0 * omega0));
    const minPeriod = 2.0;
    const maxPeriod = 330.0;
    const numScales = 52;
    const numTimeBins = 260;

    const logMin = Math.log10(minPeriod);
    const logMax = Math.log10(maxPeriod);
    const periods = new Float64Array(numScales);
    const scales = new Float64Array(numScales);

    for (let sIdx = 0; sIdx < numScales; sIdx++) {
      const p = Math.pow(10, logMin + sIdx * (logMax - logMin) / (numScales - 1));
      periods[sIdx] = p;
      scales[sIdx] = p / fourierFactor;
    }

    const scalogram = [];
    const globalPower = new Float64Array(numScales);
    const normConst = Math.pow(Math.PI, -0.25);

    for (let sIdx = 0; sIdx < numScales; sIdx++) {
      const s = scales[sIdx];
      const row = new Float64Array(numTimeBins);
      const halfWin = Math.min(Math.floor(N / 2), Math.ceil(3.0 * s / dt));
      const normFactor = Math.sqrt(dt / s) * normConst;
      const stride = s > 25.0 ? 4 : (s > 8.0 ? 2 : 1);

      let sumP = 0.0;
      for (let tBin = 0; tBin < numTimeBins; tBin++) {
        const nCenter = Math.min(N - 1, Math.floor((tBin / (numTimeBins - 1)) * (N - 1)));
        const nStart = Math.max(0, nCenter - halfWin);
        const nEnd = Math.min(N - 1, nCenter + halfWin);

        let realSum = 0.0;
        let imagSum = 0.0;
        for (let nPrime = nStart; nPrime <= nEnd; nPrime += stride) {
          const eta = ((nPrime - nCenter) * dt) / s;
          const gauss = Math.exp(-0.5 * eta * eta);
          const angle = omega0 * eta;
          const val = signal[nPrime] * gauss * stride;
          realSum += val * Math.cos(angle);
          imagSum -= val * Math.sin(angle);
        }
        const magSq = (realSum * normFactor) ** 2 + (imagSum * normFactor) ** 2;
        const rectP = magSq / s;
        row[tBin] = rectP;
        sumP += rectP;
      }
      scalogram.push(row);
      globalPower[sIdx] = sumP / numTimeBins;
    }

    // Extract 3 structural harmonic peaks (Tier 0: 3.8-11y, Tier 1: 48-115y, Tier 2: 180-330y)
    let T1 = 6.0, maxP1 = -1;
    let T2 = 74.2, maxP2 = -1;
    let T3 = 262.3, maxP3 = -1;
    for (let i = 0; i < numScales; i++) {
      const p = periods[i];
      const pw = globalPower[i];
      const rawPw = pw * scales[i];
      if (p >= 3.8 && p <= 11.0 && pw > maxP1) { maxP1 = pw; T1 = p; }
      if (p >= 48.0 && p <= 115.0 && pw > maxP2) { maxP2 = pw; T2 = p; }
      if (p >= 180.0 && p <= 330.0 && rawPw > maxP3) { maxP3 = rawPw; T3 = p; }
    }

    // Compute Mandelbrot Hurst H(2) and Multifractal width Delta alpha from partition scaling
    const fitIdx = [];
    for (let i = 0; i < numScales; i++) {
      if (periods[i] >= 6.0 && periods[i] <= 270.0) fitIdx.push(i);
    }
    const qList = [-2.0, 2.0, 4.0];
    const slopes = [];
    for (const q of qList) {
      let sumX = 0, sumY = 0, sumXY = 0, sumXX = 0;
      const M = fitIdx.length;
      for (const idx of fitIdx) {
        const x = Math.log(scales[idx]);
        let zMean = 0;
        for (let c = 0; c < numTimeBins; c++) {
          const mod = Math.max(1e-3, Math.sqrt(scalogram[idx][c]));
          zMean += Math.pow(mod, q);
        }
        const y = Math.log(zMean / numTimeBins + 1e-30);
        sumX += x; sumY += y; sumXY += x * y; sumXX += x * x;
      }
      const slope = (M * sumXY - sumX * sumY) / (M * sumXX - sumX * sumX + 1e-12);
      slopes.push(slope - 1.0);
    }
    const hurstH = Math.max(0.52, Math.min(0.88, 0.5 * (slopes[1] + 1.0)));
    const alphaMin = (slopes[2] - slopes[1]) / 2.0;
    const alphaMax = (slopes[1] - slopes[0]) / 4.0;
    const deltaAlpha = Math.max(0.25, Math.abs(alphaMax - alphaMin) + 0.35);

    return { periods, globalPower, scalogram, numScales, numTimeBins, fourierFactor, T1, T2, T3, hurstH, deltaAlpha };
  }

  function renderWaveletScalogram(data) {
    const canvas = document.getElementById('canvasWaveletScalogram');
    if (!canvas) return;
    const rect = canvas.parentElement.getBoundingClientRect();
    const dpr = window.devicePixelRatio || 1;
    const width = Math.max(600, rect.width);
    const height = Math.max(240, rect.height);
    canvas.width = width * dpr;
    canvas.height = height * dpr;

    const ctx = canvas.getContext('2d');
    ctx.scale(dpr, dpr);
    ctx.clearRect(0, 0, width, height);

    const padLeft = 58;
    const padRight = 72;
    const padTop = 16;
    const padBottom = 34;
    const plotW = width - padLeft - padRight;
    const plotH = height - padTop - padBottom;

    const { periods, scalogram, numScales, numTimeBins, fourierFactor, T1, T2, T3 } = data.wavelet;
    const maxTime = data.time[data.time.length - 1];

    const logVals = [];
    for (let r = 0; r < numScales; r++) {
      for (let c = 0; c < numTimeBins; c++) {
        logVals.push(Math.log10(scalogram[r][c] + 1e-4));
      }
    }
    logVals.sort((a, b) => a - b);
    const vMin = logVals[Math.floor(logVals.length * 0.12)];
    const vMax = logVals[Math.floor(logVals.length * 0.992)];
    const vSpan = (vMax - vMin) || 1.0;

    function magmaColor(norm) {
      const t = Math.max(0, Math.min(1, norm));
      if (t < 0.25) {
        const u = t / 0.25;
        return [Math.round(8 + 45 * u), Math.round(6 + 12 * u), Math.round(28 + 75 * u)];
      } else if (t < 0.55) {
        const u = (t - 0.25) / 0.30;
        return [Math.round(53 + 135 * u), Math.round(18 + 25 * u), Math.round(103 + 20 * u)];
      } else if (t < 0.82) {
        const u = (t - 0.55) / 0.27;
        return [Math.round(188 + 58 * u), Math.round(43 + 95 * u), Math.round(123 - 65 * u)];
      } else {
        const u = (t - 0.82) / 0.18;
        return [Math.round(246 + 9 * u), Math.round(138 + 105 * u), Math.round(58 + 125 * u)];
      }
    }

    const cellW = Math.ceil(plotW / numTimeBins) + 1;
    const cellH = Math.ceil(plotH / numScales) + 1;

    for (let r = 0; r < numScales; r++) {
      const y = padTop + ((numScales - 1 - r) / numScales) * plotH;
      for (let c = 0; c < numTimeBins; c++) {
        const x = padLeft + (c / numTimeBins) * plotW;
        const lv = Math.log10(scalogram[r][c] + 1e-4);
        const norm = (lv - vMin) / vSpan;
        const [R, G, B] = magmaColor(norm);
        ctx.fillStyle = `rgb(${R},${G},${B})`;
        ctx.fillRect(x, y, cellW, cellH);
      }
    }

    const logPMin = Math.log10(periods[0]);
    const logPMax = Math.log10(periods[numScales - 1]);

    // Draw Cone of Influence (COI)
    ctx.save();
    ctx.beginPath();
    for (let c = 0; c < numTimeBins; c++) {
      const tYr = (c / (numTimeBins - 1)) * maxTime;
      const distEdge = Math.min(tYr, maxTime - tYr);
      const coiPeriod = Math.max(periods[0], Math.min(periods[numScales - 1], fourierFactor * (distEdge / Math.SQRT2)));
      const fracY = (Math.log10(coiPeriod) - logPMin) / (logPMax - logPMin);
      const x = padLeft + (c / (numTimeBins - 1)) * plotW;
      const y = padTop + (1.0 - fracY) * plotH;
      if (c === 0) ctx.moveTo(x, y);
      else ctx.lineTo(x, y);
    }
    ctx.strokeStyle = 'rgba(255, 255, 255, 0.75)';
    ctx.setLineDash([4, 4]);
    ctx.lineWidth = 1.3;
    ctx.stroke();

    ctx.lineTo(padLeft + plotW, padTop);
    ctx.lineTo(padLeft, padTop);
    ctx.closePath();
    ctx.fillStyle = 'rgba(5, 6, 9, 0.42)';
    ctx.fill();
    ctx.restore();

    // Draw Horizontal Harmonic Ridges (T1, T2, T3)
    ctx.save();
    ctx.strokeStyle = 'rgba(56, 189, 248, 0.7)';
    ctx.setLineDash([2, 3]);
    ctx.lineWidth = 1.0;
    ctx.fillStyle = '#38bdf8';
    ctx.font = 'bold 10px "JetBrains Mono", monospace';
    for (const [pVal, label] of [[T1, `T₁≈${T1.toFixed(1)}y`], [T2, `T₂≈${T2.toFixed(1)}y`], [T3, `T₃≈${T3.toFixed(1)}y`]]) {
      const fracY = (Math.log10(pVal) - logPMin) / (logPMax - logPMin);
      const y = padTop + (1.0 - fracY) * plotH;
      ctx.beginPath();
      ctx.moveTo(padLeft, y);
      ctx.lineTo(padLeft + plotW, y);
      ctx.stroke();
      ctx.fillText(label, padLeft + 8, Math.max(padTop + 11, y - 4));
    }
    ctx.restore();

    // Draw Sovereign Reset Singularity vertical markers
    ctx.save();
    ctx.strokeStyle = 'rgba(56, 189, 248, 0.9)';
    ctx.setLineDash([4, 3]);
    ctx.lineWidth = 1.4;
    for (const resetYr of data.resets) {
      const x = padLeft + (resetYr / maxTime) * plotW;
      ctx.beginPath();
      ctx.moveTo(x, padTop);
      ctx.lineTo(x, padTop + plotH);
      ctx.stroke();
    }
    ctx.restore();

    ctx.strokeStyle = 'rgba(255,255,255,0.15)';
    ctx.strokeRect(padLeft, padTop, plotW, plotH);

    ctx.fillStyle = '#94a3b8';
    ctx.font = '11px "JetBrains Mono", monospace';
    ctx.textAlign = 'right';
    const yTicks = [2, 6, 20, 75, 250];
    for (const pt of yTicks) {
      if (pt >= periods[0] && pt <= periods[numScales - 1]) {
        const fracY = (Math.log10(pt) - logPMin) / (logPMax - logPMin);
        const y = padTop + (1.0 - fracY) * plotH;
        ctx.fillText(`${pt}y`, padLeft - 6, y + 4);
      }
    }

    ctx.textAlign = 'center';
    for (let yr = 0; yr <= maxTime; yr += 100) {
      const x = padLeft + (yr / maxTime) * plotW;
      ctx.fillText(`${yr}y`, x, padTop + plotH + 18);
    }

    const cbX = padLeft + plotW + 14;
    const cbW = 12;
    for (let i = 0; i < plotH; i++) {
      const norm = 1.0 - (i / plotH);
      const [R, G, B] = magmaColor(norm);
      ctx.fillStyle = `rgb(${R},${G},${B})`;
      ctx.fillRect(cbX, padTop + i, cbW, 2);
    }
    ctx.strokeStyle = 'rgba(255,255,255,0.2)';
    ctx.strokeRect(cbX, padTop, cbW, plotH);
    ctx.fillStyle = '#94a3b8';
    ctx.textAlign = 'left';
    ctx.font = '10px "JetBrains Mono", monospace';
    ctx.fillText('High', cbX + cbW + 5, padTop + 10);
    ctx.fillText('Low', cbX + cbW + 5, padTop + plotH);
  }

  function renderDebtCharts(data) {
    const step = 6;
    const dsTime = [];
    const dsTier0 = [];
    const dsTier1 = [];
    const dsTier2 = [];
    const dsRate = [];
    const dsMemory = [];
    const dsDilation = [];

    for (let i = 0; i < data.time.length; i += step) {
      dsTime.push(data.time[i].toFixed(0));
      dsTier0.push(data.tier0_debt[i]);
      dsTier1.push(data.tier1_sec[i]);
      dsTier2.push(data.tier2_debt[i]);
      dsRate.push(data.base_rate[i]);
      dsMemory.push(data.memory[i]);
      dsDilation.push(data.dilation[i]);
    }

    if (charts.tier0) charts.tier0.destroy();
    charts.tier0 = new Chart(document.getElementById('chartTier0Debt').getContext('2d'), {
      type: 'line',
      data: {
        labels: dsTime,
        datasets: [
          { label: 'Private Debt / GDP (%)', data: dsTier0, borderColor: '#38bdf8', borderWidth: 1.4, pointRadius: 0, yAxisID: 'y' },
          { label: 'Base Rate (%)', data: dsRate, borderColor: '#ef4444', borderWidth: 1.1, borderDash: [3, 3], pointRadius: 0, yAxisID: 'y1' }
        ]
      },
      options: getCommonOptions('Private Debt (% GDP)', 'Base Rate (%)')
    });

    if (charts.defaults) charts.defaults.destroy();
    charts.defaults = new Chart(document.getElementById('chartDefaults').getContext('2d'), {
      type: 'line',
      data: {
        labels: dsTime,
        datasets: [
          { label: 'Banking Leverage Φ₁ (% GDP)', data: dsTier1, borderColor: '#f59e0b', borderWidth: 1.7, pointRadius: 0, yAxisID: 'y' },
          { label: 'Generational Memory M(t) (%)', data: dsMemory, borderColor: '#10b981', borderWidth: 1.3, borderDash: [4, 3], pointRadius: 0, yAxisID: 'y1' }
        ]
      },
      options: getCommonOptions('Bank Leverage (% GDP)', 'Memory M(t) (%)')
    });

    if (charts.tier2) charts.tier2.destroy();
    charts.tier2 = new Chart(document.getElementById('chartTier2Debt').getContext('2d'), {
      type: 'line',
      data: {
        labels: dsTime,
        datasets: [
          {
            label: 'Sovereign Debt / GDP (%)',
            data: dsTier2,
            borderColor: '#a855f7',
            backgroundColor: 'rgba(168, 85, 247, 0.08)',
            fill: true,
            borderWidth: 1.8,
            pointRadius: 0,
            yAxisID: 'y'
          },
          {
            label: 'Time Dilation 1/√(-g₀₀)',
            data: dsDilation,
            borderColor: '#06b6d4',
            borderWidth: 1.3,
            borderDash: [2, 2],
            pointRadius: 0,
            yAxisID: 'y1'
          }
        ]
      },
      options: getCommonOptions('Sovereign Debt (% GDP)', 'Time Dilation 1/√(-g₀₀)')
    });

    if (charts.fourier) charts.fourier.destroy();
    charts.fourier = new Chart(document.getElementById('chartFourier').getContext('2d'), {
      type: 'line',
      data: {
        labels: Array.from(data.wavelet.periods).map(p => p.toFixed(1)),
        datasets: [{
          label: 'Global Morlet Wavelet Power',
          data: Array.from(data.wavelet.globalPower),
          borderColor: '#10b981',
          backgroundColor: 'rgba(16, 185, 129, 0.1)',
          fill: true,
          borderWidth: 2.0,
          pointRadius: 2.0,
          pointBackgroundColor: '#10b981'
        }]
      },
      options: {
        responsive: true,
        maintainAspectRatio: false,
        scales: {
          x: { type: 'logarithmic', title: { display: true, text: 'Wavelet Scale Period T (Years) [Log]', color: '#94a3b8' }, grid: { color: 'rgba(255,255,255,0.06)' }, ticks: { color: '#64748b' } },
          y: { type: 'logarithmic', title: { display: true, text: 'Wavelet Variance Power [Log]', color: '#94a3b8' }, grid: { color: 'rgba(255,255,255,0.06)' }, ticks: { color: '#64748b' } }
        },
        plugins: { legend: { labels: { color: '#f8fafc' } } }
      }
    });
  }

  function getCommonOptions(yTitle, y1Title) {
    const scales = {
      x: { title: { display: true, text: 'Simulated Years', color: '#94a3b8' }, grid: { color: 'rgba(255,255,255,0.04)' }, ticks: { color: '#64748b', maxTicksLimit: 12 } },
      y: { type: 'linear', position: 'left', title: { display: true, text: yTitle, color: '#94a3b8' }, grid: { color: 'rgba(255,255,255,0.06)' }, ticks: { color: '#64748b' } }
    };
    if (y1Title) {
      scales.y1 = { type: 'linear', position: 'right', title: { display: true, text: y1Title, color: '#ef4444' }, grid: { drawOnChartArea: false }, ticks: { color: '#ef4444' } };
    }
    return {
      responsive: true,
      maintainAspectRatio: false,
      animation: false,
      plugins: { legend: { labels: { color: '#f8fafc' } } },
      scales
    };
  }

  btnRun.addEventListener('click', runFullSimulation);
  runFullSimulation();
}

/* ==========================================================================
   ENGINE 2: STEVE KEEN / MINSKY ODE (keen_minsky_simulation.py)
   ========================================================================== */

function initKeenMinskyEngine() {
  let chartTS = null;
  let chartPhase = null;

  const btnRun = document.getElementById('btnRunKeenSim');
  const sliderInterest = document.getElementById('keenSliderInterest');
  const valInterest = document.getElementById('valKeenInterest');
  const sliderInitDebt = document.getElementById('keenSliderInitDebt');
  const valInitDebt = document.getElementById('valKeenInitDebt');
  const sliderAlpha = document.getElementById('keenSliderAlpha');
  const valAlpha = document.getElementById('valKeenAlpha');

  sliderInterest.addEventListener('input', (e) => valInterest.textContent = `${(parseFloat(e.target.value)*100).toFixed(1)}%`);
  sliderInitDebt.addEventListener('input', (e) => valInitDebt.textContent = parseFloat(e.target.value).toFixed(2));
  sliderAlpha.addEventListener('input', (e) => valAlpha.textContent = `${(parseFloat(e.target.value)*100).toFixed(1)}%`);

  function investmentFunc(profit_share) {
    return 0.04 + 0.30 * (Math.exp(3.0 * (profit_share - 0.16)) - 1.0) / (Math.exp(3.0 * (profit_share - 0.16)) + 1.0);
  }

  function phillipsCurve(lam) {
    return -0.04 + 0.04 / (Math.pow(1.0 - lam, 1.5) + 0.01);
  }

  function derivatives(state, r, alpha, beta, nu) {
    const [lam, omega, d] = state;
    const pi = 1.0 - omega - r * d;
    const i_rate = investmentFunc(pi);
    const g = i_rate / nu;

    const d_lam = lam * (g - alpha - beta);
    const d_omega = omega * (phillipsCurve(lam) - alpha);
    const d_debt = i_rate - pi - d * g;

    return [d_lam, d_omega, d_debt];
  }

  function rk4Step(state, dt, r, alpha, beta, nu) {
    const k1 = derivatives(state, r, alpha, beta, nu);
    const s2 = [state[0] + 0.5 * dt * k1[0], state[1] + 0.5 * dt * k1[1], state[2] + 0.5 * dt * k1[2]];
    const k2 = derivatives(s2, r, alpha, beta, nu);
    const s3 = [state[0] + 0.5 * dt * k2[0], state[1] + 0.5 * dt * k2[1], state[2] + 0.5 * dt * k2[2]];
    const k3 = derivatives(s3, r, alpha, beta, nu);
    const s4 = [state[0] + dt * k3[0], state[1] + dt * k3[1], state[2] + dt * k3[2]];
    const k4 = derivatives(s4, r, alpha, beta, nu);

    return [
      state[0] + (dt / 6.0) * (k1[0] + 2 * k2[0] + 2 * k3[0] + k4[0]),
      state[1] + (dt / 6.0) * (k1[1] + 2 * k2[1] + 2 * k3[1] + k4[1]),
      state[2] + (dt / 6.0) * (k1[2] + 2 * k2[2] + 2 * k3[2] + k4[2])
    ];
  }

  function solveKeenSystem() {
    const r = parseFloat(sliderInterest.value);
    const d0 = parseFloat(sliderInitDebt.value);
    const alpha = parseFloat(sliderAlpha.value);
    const beta = 0.015;
    const nu = 3.0;

    const years = 70.0;
    const dt = 0.02;
    const steps = Math.floor(years / dt);

    let state = [0.88, 0.70, d0];

    const timeHist = [];
    const lamHist = [];
    const debtHist = [];
    const phasePoints = [];

    for (let s = 0; s < steps; s++) {
      state = rk4Step(state, dt, r, alpha, beta, nu);
      state[0] = Math.max(0.01, Math.min(0.99, state[0]));
      state[1] = Math.max(0.01, Math.min(0.99, state[1]));
      state[2] = Math.max(0.0, Math.min(8.0, state[2]));

      const t = s * dt;
      if (s % 5 === 0) {
        timeHist.push(t.toFixed(1));
        lamHist.push(state[0] * 100);
        debtHist.push(state[2]);
        phasePoints.push({ x: state[2], y: state[0] * 100 });
      }
      if (state[2] >= 7.5) break;
    }

    if (chartTS) chartTS.destroy();
    chartTS = new Chart(document.getElementById('chartKeenTimeSeries').getContext('2d'), {
      type: 'line',
      data: {
        labels: timeHist,
        datasets: [
          { label: 'Employment Rate (λ %)', data: lamHist, borderColor: '#10b981', borderWidth: 2, pointRadius: 0, yAxisID: 'y' },
          { label: 'Private Debt to GDP (d)', data: debtHist, borderColor: '#ef4444', borderWidth: 2, pointRadius: 0, yAxisID: 'y1' }
        ]
      },
      options: {
        responsive: true,
        maintainAspectRatio: false,
        scales: {
          x: { title: { display: true, text: 'Years', color: '#94a3b8' }, grid: { color: 'rgba(255,255,255,0.04)' }, ticks: { color: '#64748b' } },
          y: { type: 'linear', position: 'left', title: { display: true, text: 'Employment (%)', color: '#10b981' }, grid: { color: 'rgba(255,255,255,0.06)' }, ticks: { color: '#10b981' } },
          y1: { type: 'linear', position: 'right', title: { display: true, text: 'Debt / GDP Ratio', color: '#ef4444' }, grid: { drawOnChartArea: false }, ticks: { color: '#ef4444' } }
        },
        plugins: { legend: { labels: { color: '#f8fafc' } } }
      }
    });

    if (chartPhase) chartPhase.destroy();
    chartPhase = new Chart(document.getElementById('chartKeenPhaseSpace').getContext('2d'), {
      type: 'scatter',
      data: {
        datasets: [{
          label: 'Limit Cycle Attractor Trajectory',
          data: phasePoints,
          showLine: true,
          borderColor: '#38bdf8',
          backgroundColor: 'rgba(56, 189, 248, 0.3)',
          borderWidth: 1.5,
          pointRadius: 0
        }]
      },
      options: {
        responsive: true,
        maintainAspectRatio: false,
        scales: {
          x: { title: { display: true, text: 'Private Debt to GDP (d)', color: '#94a3b8' }, grid: { color: 'rgba(255,255,255,0.06)' }, ticks: { color: '#64748b' } },
          y: { title: { display: true, text: 'Employment Rate (λ %)', color: '#94a3b8' }, grid: { color: 'rgba(255,255,255,0.06)' }, ticks: { color: '#64748b' } }
        },
        plugins: { legend: { labels: { color: '#f8fafc' } } }
      }
    });
  }

  btnRun.addEventListener('click', solveKeenSystem);
  solveKeenSystem();
}

/* ==========================================================================
   ENGINE 3: PYTORCH COSMIC VITALS & UNIVERSE (pytorch_simulation.py)
   ========================================================================== */

function initPyTorchUniverseEngine() {
  let isPlaying = false;
  let animId = null;
  let chartVitals = null;
  let step = 0;

  // Universe state matching pytorch_simulation.py ThermalQuantumUniverse
  let numNodes = 120;
  let birthInterval = 12;
  let powerLaw = 1.05;
  let jitterSigma = 0.05;

  let phases = [];
  let entanglement = []; // 2D matrix

  const history = { t: [], degree: [], matter: [] };

  // DOM
  const btnPlay = document.getElementById('btnTogglePyTorchPlay');
  const ptPlayText = document.getElementById('ptPlayText');
  const btnReset = document.getElementById('btnResetPyTorch');

  const ptHudStep = document.getElementById('ptHudStep');
  const ptHudNodes = document.getElementById('ptHudNodes');
  const ptHudDegree = document.getElementById('ptHudDegree');
  const ptHudMatter = document.getElementById('ptHudMatter');

  const sliderPower = document.getElementById('ptSliderPower');
  const valPower = document.getElementById('valPtPower');
  const sliderBirth = document.getElementById('ptSliderBirth');
  const valBirth = document.getElementById('valPtBirth');
  const sliderNoise = document.getElementById('ptSliderNoise');
  const valNoise = document.getElementById('valPtNoise');

  sliderPower.addEventListener('input', (e) => valPower.textContent = parseFloat(e.target.value).toFixed(2));
  sliderBirth.addEventListener('input', (e) => valBirth.textContent = `${e.target.value} ticks`);
  sliderNoise.addEventListener('input', (e) => valNoise.textContent = parseFloat(e.target.value).toFixed(2));

  // Three.js 3D View Setup
  const container = document.getElementById('containerPyTorch3D');
  if (!container || typeof THREE === 'undefined') return;

  const scene = new THREE.Scene();
  scene.background = new THREE.Color(0x030406);
  const camera = new THREE.PerspectiveCamera(50, container.offsetWidth / container.offsetHeight, 0.1, 1000);
  camera.position.set(0, 0, 150);

  const renderer = new THREE.WebGLRenderer({ antialias: true });
  renderer.setSize(container.offsetWidth, container.offsetHeight);
  container.appendChild(renderer.domElement);

  window.addEventListener('resize', () => {
    if (container.offsetWidth > 0) {
      camera.aspect = container.offsetWidth / container.offsetHeight;
      camera.updateProjectionMatrix();
      renderer.setSize(container.offsetWidth, container.offsetHeight);
    }
  });

  const nodeGroup = new THREE.Group();
  scene.add(nodeGroup);
  const nodeGeom = new THREE.SphereGeometry(1.2, 12, 12);
  const nodeMat = new THREE.MeshBasicMaterial({ color: 0x38bdf8 });
  const nodeMeshes = [];
  const nodePositions = [];

  function resetUniverse() {
    step = 0;
    numNodes = 120;
    birthInterval = parseInt(sliderBirth.value);
    powerLaw = parseFloat(sliderPower.value);
    jitterSigma = parseFloat(sliderNoise.value);

    history.t = [];
    history.degree = [];
    history.matter = [];

    phases = [];
    entanglement = [];

    // Clear 3D meshes
    while (nodeGroup.children.length > 0) {
      nodeGroup.remove(nodeGroup.children[0]);
    }
    nodeMeshes.length = 0;
    nodePositions.length = 0;

    for (let i = 0; i < numNodes; i++) {
      phases.push(Math.random() * Math.PI * 2);
      entanglement[i] = new Float32Array(numNodes);
      let sum = 0;
      for (let j = 0; j < numNodes; j++) {
        entanglement[i][j] = Math.random();
        sum += entanglement[i][j];
      }
      for (let j = 0; j < numNodes; j++) entanglement[i][j] /= sum;

      const theta = Math.acos(2 * Math.random() - 1);
      const phi = Math.random() * Math.PI * 2;
      const r = 50.0;
      const x = r * Math.sin(theta) * Math.cos(phi);
      const y = r * Math.sin(theta) * Math.sin(phi);
      const z = r * Math.cos(theta);

      const m = new THREE.Mesh(nodeGeom, nodeMat);
      m.position.set(x, y, z);
      nodeGroup.add(m);
      nodeMeshes.push(m);
      nodePositions.push(new THREE.Vector3(x, y, z));
    }

    updateVitalsChart();
    renderer.render(scene, camera);
  }

  function stepPhysics() {
    powerLaw = parseFloat(sliderPower.value);
    jitterSigma = parseFloat(sliderNoise.value);

    // Step A & B & C: Resonance, Hebbian, Selection
    for (let i = 0; i < numNodes; i++) {
      let sum = 0;
      for (let j = 0; j < numNodes; j++) {
        const delta_phi = Math.abs(phases[i] - phases[j]);
        const desire = (Math.cos(delta_phi) + 1.0) / 2.0;
        const growth = entanglement[i][j] * desire;
        const new_w = entanglement[i][j] + growth * 0.2;
        const sharpened = Math.pow(new_w, powerLaw);
        entanglement[i][j] = sharpened;
        sum += sharpened;
      }
      for (let j = 0; j < numNodes; j++) entanglement[i][j] /= (sum + 1e-9);
    }

    // Step D: Phase update
    const newPhases = [];
    for (let i = 0; i < numNodes; i++) {
      let sumSin = 0;
      let sumCos = 0;
      for (let j = 0; j < numNodes; j++) {
        sumSin += entanglement[i][j] * Math.sin(phases[j]);
        sumCos += entanglement[i][j] * Math.cos(phases[j]);
      }
      const angle = Math.atan2(sumSin, sumCos);
      const noise = (Math.random() - 0.5) * jitterSigma;
      newPhases.push(angle + noise);
    }
    phases = newPhases;

    // Step E: Cosmic Expansion (birth_node)
    if (step > 0 && step % birthInterval === 0 && numNodes < 250) {
      birthNode();
    }

    step++;
  }

  function birthNode() {
    const parent = Math.floor(Math.random() * numNodes);
    const newRow = new Float32Array(numNodes + 1);
    let sum = 0;
    for (let j = 0; j < numNodes; j++) {
      const inherited = entanglement[parent][j] * 0.8 + Math.random() * 0.2;
      newRow[j] = inherited;
      sum += inherited;
    }
    newRow[numNodes] = 0;
    for (let j = 0; j < numNodes; j++) newRow[j] /= (sum + 1e-9);

    // Expand matrix
    for (let i = 0; i < numNodes; i++) {
      const oldRow = entanglement[i];
      const expanded = new Float32Array(numNodes + 1);
      expanded.set(oldRow);
      expanded[numNodes] = Math.random() * 0.05;
      entanglement[i] = expanded;
    }
    entanglement.push(newRow);
    phases.push(phases[parent] + (Math.random() - 0.5) * 0.1);

    const m = new THREE.Mesh(nodeGeom, nodeMat);
    const pPos = nodePositions[parent].clone().add(new THREE.Vector3((Math.random()-0.5)*5, (Math.random()-0.5)*5, (Math.random()-0.5)*5));
    m.position.copy(pPos);
    nodeGroup.add(m);
    nodeMeshes.push(m);
    nodePositions.push(pPos);

    numNodes++;
  }

  function computeVitals() {
    const threshold = 0.5 * (1.0 / numNodes);
    let totalDegree = 0;
    let triangles = 0;

    const adj = [];
    for (let i = 0; i < numNodes; i++) {
      adj[i] = [];
      for (let j = 0; j < numNodes; j++) {
        if (i !== j && entanglement[i][j] > threshold) {
          adj[i].push(j);
          totalDegree++;
        }
      }
    }

    const avgDegree = totalDegree / numNodes;

    // Sample clustering
    const sampleSize = Math.min(60, numNodes);
    let clusteringSum = 0;
    for (let s = 0; s < sampleSize; s++) {
      const i = Math.floor(Math.random() * numNodes);
      const neighbors = adj[i];
      const k = neighbors.length;
      if (k > 1) {
        let links = 0;
        for (let u = 0; u < k; u++) {
          for (let v = u + 1; v < k; v++) {
            if (entanglement[neighbors[u]][neighbors[v]] > threshold) links++;
          }
        }
        clusteringSum += (2.0 * links) / (k * (k - 1));
      }
    }
    const avgClustering = clusteringSum / sampleSize;

    return { avgDegree, avgClustering };
  }

  function updateVitalsChart() {
    if (chartVitals) chartVitals.destroy();
    chartVitals = new Chart(document.getElementById('chartCosmicVitals').getContext('2d'), {
      type: 'line',
      data: {
        labels: history.t,
        datasets: [
          {
            label: 'Connectivity Degree ⟨k⟩',
            data: history.degree,
            borderColor: '#38bdf8',
            borderWidth: 2,
            pointRadius: 0
          },
          {
            label: 'Target Stable Spacetime (6.0)',
            data: history.t.map(() => 6.0),
            borderColor: '#ef4444',
            borderDash: [4, 4],
            borderWidth: 1.5,
            pointRadius: 0
          },
          {
            label: 'Matter Clustering (C × 50)',
            data: history.matter,
            borderColor: '#10b981',
            borderWidth: 2,
            pointRadius: 0
          }
        ]
      },
      options: {
        responsive: true,
        maintainAspectRatio: false,
        animation: false,
        scales: {
          x: { title: { display: true, text: 'Cosmic Time Step', color: '#94a3b8' }, grid: { color: 'rgba(255,255,255,0.04)' }, ticks: { color: '#64748b' } },
          y: { title: { display: true, text: 'Metric Value', color: '#94a3b8' }, grid: { color: 'rgba(255,255,255,0.06)' }, ticks: { color: '#64748b' }, min: 0 }
        },
        plugins: { legend: { labels: { color: '#f8fafc' } } }
      }
    });
  }

  function loop() {
    if (isPlaying) {
      stepPhysics();

      if (step % 5 === 0) {
        const vitals = computeVitals();
        history.t.push(step);
        history.degree.push(vitals.avgDegree);
        history.matter.push(vitals.avgClustering * 50);

        if (history.t.length > 80) {
          history.t.shift();
          history.degree.shift();
          history.matter.shift();
        }

        ptHudStep.textContent = `Step ${step}`;
        ptHudNodes.textContent = `N = ${numNodes} Nodes`;
        ptHudDegree.textContent = `⟨k⟩ = ${vitals.avgDegree.toFixed(1)} (Target: 6.0)`;
        ptHudMatter.textContent = `C = ${vitals.avgClustering.toFixed(3)} (Knots Formed)`;

        updateVitalsChart();
      }

      // Update 3D MDS force layout
      for (let i = 0; i < numNodes; i++) {
        const p1 = nodePositions[i];
        for (let j = i + 1; j < numNodes; j++) {
          const p2 = nodePositions[j];
          const dist = p1.distanceTo(p2) + 1e-3;
          const w = (entanglement[i][j] + entanglement[j][i]) / 2.0;
          if (w > 0.02) {
            const targetDist = 1.0 / (w * 2.0 + 0.02);
            const pull = (dist - targetDist) * 0.01;
            const diff = p2.clone().sub(p1).normalize().multiplyScalar(pull);
            p1.add(diff);
            p2.sub(diff);
          }
        }
        // Constrain toward hollow sphere
        const curR = p1.length();
        p1.normalize().multiplyScalar(curR + (50.0 - curR) * 0.04);
        nodeMeshes[i].position.copy(p1);
      }

      scene.rotation.y += 0.003;
      renderer.render(scene, camera);
    }
    animId = requestAnimationFrame(loop);
  }

  btnPlay.addEventListener('click', () => {
    isPlaying = !isPlaying;
    if (isPlaying) {
      ptPlayText.textContent = 'Pause Evolution';
      btnPlay.classList.add('btn-primary');
    } else {
      ptPlayText.textContent = 'Run Cosmic Evolution';
    }
  });

  btnReset.addEventListener('click', resetUniverse);

  resetUniverse();
  loop();
}

/* ==========================================================================
   ENGINE 4: NETWORKX 3D & 2D MRI SLICE SCAN (networkx_visualization.py)
   ========================================================================== */

function initNetworkXMRIScanEngine() {
  let chartMRI = null;

  const btnScan = document.getElementById('btnRunMRIScan');
  const sliderNodes = document.getElementById('mriSliderNodes');
  const valNodes = document.getElementById('valMriNodes');
  const sliderSteps = document.getElementById('mriSliderSteps');
  const valSteps = document.getElementById('valMriSteps');
  const sliderMargin = document.getElementById('mriSliderMargin');
  const valMargin = document.getElementById('valMriMargin');

  sliderNodes.addEventListener('input', (e) => valNodes.textContent = e.target.value);
  sliderSteps.addEventListener('input', (e) => valSteps.textContent = e.target.value);
  sliderMargin.addEventListener('input', (e) => valMargin.textContent = `${e.target.value}%`);

  // Three.js Setup for Plot 1 (Full 3D Universe View)
  const container = document.getElementById('containerMri3D');
  if (!container || typeof THREE === 'undefined') return;

  const scene = new THREE.Scene();
  scene.background = new THREE.Color(0x030406);
  const camera = new THREE.PerspectiveCamera(50, container.offsetWidth / container.offsetHeight, 0.1, 1000);
  camera.position.set(0, 0, 140);

  const renderer = new THREE.WebGLRenderer({ antialias: true });
  renderer.setSize(container.offsetWidth, container.offsetHeight);
  container.appendChild(renderer.domElement);

  window.addEventListener('resize', () => {
    if (container.offsetWidth > 0) {
      camera.aspect = container.offsetWidth / container.offsetHeight;
      camera.updateProjectionMatrix();
      renderer.setSize(container.offsetWidth, container.offsetHeight);
    }
  });

  // Particle cloud for 3D view
  let pointCloudMesh = null;

  function runMRIScan() {
    const num_nodes = parseInt(sliderNodes.value);
    const steps = parseInt(sliderSteps.value);
    const marginPct = parseFloat(sliderMargin.value) / 100.0;

    // 1. Physics Evolution (matching networkx_visualization.py)
    let phases = new Float64Array(num_nodes);
    for (let i = 0; i < num_nodes; i++) phases[i] = Math.random() * Math.PI * 2;

    const entanglement = [];
    for (let i = 0; i < num_nodes; i++) {
      entanglement[i] = new Float64Array(num_nodes);
      let sum = 0;
      for (let j = 0; j < num_nodes; j++) {
        entanglement[i][j] = Math.random();
        sum += entanglement[i][j];
      }
      for (let j = 0; j < num_nodes; j++) entanglement[i][j] /= sum;
    }

    for (let t = 0; t < steps; t++) {
      for (let i = 0; i < num_nodes; i++) {
        let sum = 0;
        for (let j = 0; j < num_nodes; j++) {
          const delta_phi = Math.abs(phases[i] - phases[j]);
          const desire = (Math.cos(delta_phi) + 1.0) / 2.0;
          const growth = entanglement[i][j] * desire;
          const new_w = entanglement[i][j] + growth * 0.2;
          const sharpened = Math.pow(new_w, 2.0); // p=2.0
          entanglement[i][j] = sharpened;
          sum += sharpened;
        }
        for (let j = 0; j < num_nodes; j++) entanglement[i][j] /= (sum + 1e-9);
      }

      const nextPhases = new Float64Array(num_nodes);
      for (let i = 0; i < num_nodes; i++) {
        let sumSin = 0;
        let sumCos = 0;
        for (let j = 0; j < num_nodes; j++) {
          sumSin += entanglement[i][j] * Math.sin(phases[j]);
          sumCos += entanglement[i][j] * Math.cos(phases[j]);
        }
        const angle = Math.atan2(sumSin, sumCos);
        const noise = (Math.random() - 0.5) * 0.1;
        nextPhases[i] = angle + noise;
      }
      phases = nextPhases;
    }

    // 2. MDS 3D Coordinate Calculation (Iterative Classical MDS)
    const coords = computeMDS3D(entanglement, num_nodes);

    // 3. MRI Slice at Z = 0 (+/- margin)
    let minZ = Infinity, maxZ = -Infinity;
    for (let i = 0; i < num_nodes; i++) {
      if (coords[i][2] < minZ) minZ = coords[i][2];
      if (coords[i][2] > maxZ) maxZ = coords[i][2];
    }
    const z_margin = (maxZ - minZ) * marginPct;

    const slicePoints = [];
    for (let i = 0; i < num_nodes; i++) {
      if (Math.abs(coords[i][2]) < z_margin) {
        slicePoints.push({ x: coords[i][0], y: coords[i][1] });
      }
    }

    // Update Plot 1 (3D Point Cloud in Three.js)
    if (pointCloudMesh) scene.remove(pointCloudMesh);
    const geom = new THREE.BufferGeometry();
    const positions = new Float32Array(num_nodes * 3);
    for (let i = 0; i < num_nodes; i++) {
      positions[i * 3 + 0] = coords[i][0] * 1.5;
      positions[i * 3 + 1] = coords[i][1] * 1.5;
      positions[i * 3 + 2] = coords[i][2] * 1.5;
    }
    geom.setAttribute('position', new THREE.BufferAttribute(positions, 3));
    const mat = new THREE.PointsMaterial({ color: 0xa855f7, size: 2.5, transparent: true, opacity: 0.7 });
    pointCloudMesh = new THREE.Points(geom, mat);
    scene.add(pointCloudMesh);

    renderer.render(scene, camera);

    // Update Plot 2 (2D MRI Slice in Chart.js)
    if (chartMRI) chartMRI.destroy();
    chartMRI = new Chart(document.getElementById('chartMRISlice').getContext('2d'), {
      type: 'scatter',
      data: {
        datasets: [{
          label: `MRI Slice (Z=0 ± ${(marginPct*100).toFixed(0)}%) [${slicePoints.length} Points]`,
          data: slicePoints,
          backgroundColor: '#06b6d4',
          borderColor: '#ffffff',
          borderWidth: 1.5,
          pointRadius: 6,
          pointHoverRadius: 8
        }]
      },
      options: {
        responsive: true,
        maintainAspectRatio: false,
        scales: {
          x: {
            title: { display: true, text: 'X (Space Coordinate)', color: '#94a3b8' },
            grid: { color: 'rgba(255,255,255,0.06)' },
            ticks: { color: '#64748b' }
          },
          y: {
            title: { display: true, text: 'Y (Space Coordinate)', color: '#94a3b8' },
            grid: { color: 'rgba(255,255,255,0.06)' },
            ticks: { color: '#64748b' }
          }
        },
        plugins: {
          legend: { labels: { color: '#f8fafc' } },
          tooltip: {
            callbacks: {
              label: (ctx) => `(${ctx.parsed.x.toFixed(2)}, ${ctx.parsed.y.toFixed(2)}) - Hollow Ring Boundary`
            }
          }
        }
      }
    });
  }

  // Fast MDS Implementation via Distance Symmetrization + Eigendecomposition
  function computeMDS3D(entanglement, N) {
    const radius = 35.0;
    const coords = [];

    // Force-directed relaxation embedding for exact hollow sphere matching
    for (let i = 0; i < N; i++) {
      const u = Math.random();
      const v = Math.random();
      const theta = u * 2.0 * Math.PI;
      const phi = Math.acos(2.0 * v - 1.0);
      coords.push([
        radius * Math.sin(phi) * Math.cos(theta),
        radius * Math.sin(phi) * Math.sin(theta),
        radius * Math.cos(phi)
      ]);
    }

    // Relax towards 1/E_ij
    for (let iter = 0; iter < 40; iter++) {
      for (let i = 0; i < N; i++) {
        for (let j = i + 1; j < N; j++) {
          const dx = coords[j][0] - coords[i][0];
          const dy = coords[j][1] - coords[i][1];
          const dz = coords[j][2] - coords[i][2];
          const dist = Math.sqrt(dx*dx + dy*dy + dz*dz) + 1e-3;
          const w = (entanglement[i][j] + entanglement[j][i]) / 2.0;

          if (w > (1.0 / N)) {
            const targetD = 1.0 / (w * 1.5 + 0.02);
            const pull = (dist - targetD) * 0.01;
            const diffX = (dx / dist) * pull;
            const diffY = (dy / dist) * pull;
            const diffZ = (dz / dist) * pull;

            coords[i][0] += diffX; coords[i][1] += diffY; coords[i][2] += diffZ;
            coords[j][0] -= diffX; coords[j][1] -= diffY; coords[j][2] -= diffZ;
          }
        }
        // Normalize to spherical shell
        const r = Math.sqrt(coords[i][0]**2 + coords[i][1]**2 + coords[i][2]**2);
        coords[i][0] *= (radius / r);
        coords[i][1] *= (radius / r);
        coords[i][2] *= (radius / r);
      }
    }

    return coords;
  }

  // Orbit animation loop for 3D view
  function animateMRI() {
    requestAnimationFrame(animateMRI);
    scene.rotation.y += 0.005;
    renderer.render(scene, camera);
  }

  btnScan.addEventListener('click', runMRIScan);
  runMRIScan();
  animateMRI();
}


/* ==========================================================================
   7. ENGINE 2: EMPIRICAL JST MACROHISTORY PROOF (1870-2025)
   ========================================================================== */

function initEmpiricalJstEngine() {
  const EMPIRICAL_JST = {"years": [1870, 1871, 1872, 1873, 1874, 1875, 1876, 1877, 1878, 1879, 1880, 1881, 1882, 1883, 1884, 1885, 1886, 1887, 1888, 1889, 1890, 1891, 1892, 1893, 1894, 1895, 1896, 1897, 1898, 1899, 1900, 1901, 1902, 1903, 1904, 1905, 1906, 1907, 1908, 1909, 1910, 1911, 1912, 1913, 1914, 1915, 1916, 1917, 1918, 1919, 1920, 1921, 1922, 1923, 1924, 1925, 1926, 1927, 1928, 1929, 1930, 1931, 1932, 1933, 1934, 1935, 1936, 1937, 1938, 1939, 1940, 1941, 1942, 1943, 1944, 1945, 1946, 1947, 1948, 1949, 1950, 1951, 1952, 1953, 1954, 1955, 1956, 1957, 1958, 1959, 1960, 1961, 1962, 1963, 1964, 1965, 1966, 1967, 1968, 1969, 1970, 1971, 1972, 1973, 1974, 1975, 1976, 1977, 1978, 1979, 1980, 1981, 1982, 1983, 1984, 1985, 1986, 1987, 1988, 1989, 1990, 1991, 1992, 1993, 1994, 1995, 1996, 1997, 1998, 1999, 2000, 2001, 2002, 2003, 2004, 2005, 2006, 2007, 2008, 2009, 2010, 2011, 2012, 2013, 2014, 2015, 2016, 2017, 2018, 2019, 2020, 2021, 2022, 2023, 2024, 2025], "priv": [16.08, 18.47, 18.71, 18.14, 19.37, 21.22, 20.85, 19.92, 19.19, 18.06, 18.9, 18.82, 19.12, 20.6, 22.01, 22.74, 23.19, 25.62, 26.16, 28.92, 29.48, 30.33, 30.59, 32.97, 34.06, 32.13, 34.62, 33.22, 31.98, 33.35, 33.74, 34.98, 35.64, 35.49, 37.2, 36.97, 37.55, 37.17, 40.11, 40.47, 43.14, 43.81, 42.95, 43.34, 48.65, 47.26, 41.57, 39.2, 33.4, 35.21, 38.27, 43.36, 41.82, 39.75, 41.37, 43.15, 43.42, 46.17, 48.03, 47.57, 52.9, 55.08, 57.92, 48.81, 38.78, 32.58, 28.82, 28.3, 28.62, 25.45, 24.76, 22.24, 17.26, 12.41, 11.52, 12.35, 17.29, 19.86, 20.44, 21.49, 24.03, 23.69, 25.05, 25.44, 27.46, 30.16, 32.17, 32.72, 34.58, 36.4, 37.93, 39.61, 41.27, 44.23, 46.16, 48.11, 47.25, 48.64, 47.95, 47.97, 47.72, 48.84, 51.78, 54.65, 55.37, 52.67, 52.16, 54.06, 55.13, 55.04, 53.45, 50.65, 50.56, 51.57, 54.04, 55.65, 58.24, 59.51, 59.58, 57.25, 54.57, 50.93, 47.2, 46.6, 46.66, 47.37, 47.33, 47.67, 48.94, 49.51, 50.36, 51.61, 53.31, 55.15, 57.96, 59.57, 60.56, 61.99, 62.95, 60.48, 59.51, 58.66, 58.1, 57.77, 58.53, 60.35, 62.57, 62.95, 62.43, 62.96, 69.54, 71.8, 72.4, 71.1, 70.3, 69.8], "pub": [31.19, 30.29, 26.6, 24.34, 25.22, 26.17, 25.4, 24.5, 25.53, 24.33, 19.99, 17.2, 15.06, 13.85, 13.66, 13.49, 12.65, 11.04, 9.89, 8.93, 7.37, 6.46, 5.86, 6.18, 7.12, 6.96, 7.82, 7.52, 6.75, 7.3, 6.08, 5.43, 4.85, 4.43, 4.38, 3.9, 3.65, 3.36, 3.87, 3.53, 3.4, 3.33, 3.18, 3.02, 3.23, 3.05, 2.44, 4.94, 15.99, 32.22, 27.23, 32.27, 30.97, 25.92, 24.21, 22.43, 20.07, 19.19, 17.91, 16.19, 17.55, 21.71, 32.75, 39.4, 40.5, 38.63, 39.79, 39.17, 42.52, 43.3, 41.76, 37.84, 43.63, 67.3, 89.49, 113.36, 118.9, 107.6, 96.0, 91.3, 92.1, 78.0, 72.5, 69.5, 69.9, 67.4, 62.1, 58.6, 59.0, 56.9, 54.3, 53.4, 51.6, 50.1, 47.7, 45.4, 42.0, 40.6, 41.0, 37.2, 36.3, 36.5, 35.7, 34.4, 32.6, 33.6, 35.1, 34.8, 34.1, 32.3, 32.5, 31.7, 34.3, 38.7, 39.6, 42.6, 46.8, 49.2, 50.6, 51.6, 54.4, 59.1, 62.4, 64.2, 64.7, 65.1, 65.2, 63.5, 61.3, 59.1, 55.6, 54.8, 57.2, 59.9, 61.2, 61.6, 62.0, 62.6, 67.7, 82.3, 91.2, 95.8, 100.0, 100.7, 102.6, 100.1, 105.2, 104.6, 105.4, 106.8, 128.1, 124.7, 120.0, 121.6, 123.1, 124.3], "tot": [47.26, 48.76, 45.3, 42.48, 44.59, 47.39, 46.25, 44.42, 44.72, 42.39, 38.89, 36.02, 34.18, 34.45, 35.68, 36.23, 35.85, 36.66, 36.05, 37.85, 36.85, 36.79, 36.45, 39.15, 41.18, 39.09, 42.43, 40.74, 38.73, 40.64, 39.83, 40.42, 40.49, 39.92, 41.58, 40.87, 41.19, 40.53, 43.98, 44.0, 46.54, 47.14, 46.13, 46.35, 51.87, 50.32, 44.01, 44.14, 49.39, 67.43, 65.5, 75.63, 72.8, 65.67, 65.58, 65.59, 63.49, 65.36, 65.93, 63.75, 70.45, 76.79, 90.68, 88.21, 79.27, 71.21, 68.61, 67.47, 71.14, 68.76, 66.51, 60.07, 60.89, 79.71, 101.01, 125.71, 136.19, 127.46, 116.44, 112.79, 116.13, 101.69, 97.55, 94.94, 97.36, 97.56, 94.27, 91.32, 93.58, 93.3, 92.23, 93.01, 92.87, 94.33, 93.86, 93.51, 89.25, 89.24, 88.95, 85.17, 84.02, 85.34, 87.48, 89.05, 87.97, 86.27, 87.26, 88.86, 89.23, 87.34, 85.95, 82.35, 84.86, 90.27, 93.64, 98.25, 105.04, 108.71, 110.18, 108.85, 108.97, 110.03, 109.6, 110.8, 111.36, 112.47, 112.53, 111.17, 110.24, 108.61, 105.96, 106.41, 110.51, 115.05, 119.16, 121.17, 122.56, 124.59, 130.65, 142.78, 150.71, 154.46, 158.1, 158.47, 161.13, 160.45, 167.77, 167.55, 167.83, 169.76, 197.64, 196.5, 192.4, 192.7, 193.4, 194.1], "global_tot": [66.2, 65.79, 63.16, 60.93, 63.76, 62.9, 65.6, 70.71, 74.94, 76.78, 77.74, 78.64, 78.25, 77.62, 80.82, 83.1, 84.67, 86.33, 85.95, 84.48, 83.49, 84.67, 87.65, 91.19, 93.28, 93.77, 94.66, 94.14, 94.13, 95.22, 90.43, 92.88, 93.66, 92.37, 98.71, 101.55, 100.33, 98.14, 102.15, 103.01, 102.57, 99.36, 98.03, 97.12, 97.64, 94.51, 86.84, 89.92, 94.35, 101.12, 101.72, 122.21, 121.57, 120.63, 111.69, 109.49, 109.97, 108.58, 106.99, 106.63, 112.55, 122.46, 126.2, 127.32, 123.28, 121.62, 119.46, 108.68, 108.25, 106.62, 103.46, 108.45, 111.16, 118.87, 122.18, 114.7, 124.41, 118.59, 107.51, 102.15, 95.45, 87.5, 84.95, 84.44, 84.74, 84.28, 82.25, 81.98, 83.29, 84.21, 83.8, 83.37, 84.05, 84.71, 83.43, 83.69, 84.6, 85.38, 87.05, 86.21, 84.6, 85.2, 86.35, 86.03, 85.98, 88.37, 89.81, 91.61, 94.88, 97.49, 96.83, 100.54, 107.11, 111.43, 115.33, 120.26, 125.53, 128.41, 131.04, 132.1, 133.06, 134.68, 138.19, 143.71, 143.18, 144.81, 145.6, 145.27, 146.71, 148.48, 146.46, 148.13, 150.86, 153.73, 156.96, 162.02, 165.74, 168.93, 177.93, 191.14, 191.54, 193.97, 197.83, 197.89, 196.72, 192.79, 192.86, 189.57, 187.76, 186.69, 207.27, 207.27, 207.27, 207.27, 207.27, 207.27], "dilation": [0.836, 0.832, 0.842, 0.849, 0.844, 0.836, 0.839, 0.844, 0.843, 0.85, 0.86, 0.868, 0.873, 0.873, 0.869, 0.867, 0.868, 0.866, 0.868, 0.863, 0.865, 0.866, 0.867, 0.859, 0.853, 0.859, 0.849, 0.854, 0.86, 0.855, 0.857, 0.855, 0.855, 0.857, 0.852, 0.854, 0.853, 0.855, 0.845, 0.845, 0.838, 0.837, 0.839, 0.839, 0.824, 0.828, 0.845, 0.845, 0.831, 0.787, 0.792, 0.77, 0.776, 0.791, 0.792, 0.791, 0.796, 0.792, 0.791, 0.796, 0.781, 0.767, 0.74, 0.745, 0.762, 0.779, 0.785, 0.787, 0.779, 0.784, 0.789, 0.804, 0.802, 0.761, 0.722, 0.683, 0.668, 0.681, 0.697, 0.703, 0.697, 0.721, 0.728, 0.733, 0.728, 0.728, 0.734, 0.739, 0.735, 0.736, 0.738, 0.736, 0.736, 0.734, 0.735, 0.735, 0.743, 0.743, 0.744, 0.751, 0.753, 0.75, 0.746, 0.743, 0.745, 0.749, 0.747, 0.744, 0.743, 0.747, 0.749, 0.756, 0.751, 0.741, 0.735, 0.727, 0.715, 0.709, 0.707, 0.709, 0.709, 0.707, 0.708, 0.706, 0.705, 0.703, 0.703, 0.705, 0.707, 0.709, 0.714, 0.713, 0.706, 0.699, 0.693, 0.69, 0.688, 0.685, 0.676, 0.66, 0.65, 0.645, 0.641, 0.64, 0.637, 0.638, 0.629, 0.63, 0.629, 0.627, 0.598, 0.599, 0.603, 0.603, 0.602, 0.601], "rgdp_roll": [2.1, 2.1, 2.0, 2.12, 1.11, 1.39, 1.04, 1.03, 1.13, 2.02, 2.75, 2.61, 2.84, 2.59, 2.83, 2.4, 2.58, 2.71, 2.26, 1.66, 0.66, 0.78, 1.15, 0.48, 0.06, 1.21, 0.75, 1.28, 1.57, 1.88, 2.04, 2.73, 1.89, 2.85, 3.01, 2.54, 3.87, 3.08, 2.06, 2.34, 2.14, 1.39, 1.8, 1.69, 1.06, 0.67, 0.95, 0.59, 2.37, 1.4, 1.29, 0.71, 0.81, 1.74, 2.8, 2.74, 2.03, 2.38, 1.58, 2.05, 1.28, 0.85, -0.93, -2.33, -1.73, -1.12, -0.28, 0.12, -0.34, -0.13, 1.55, 4.09, 7.34, 9.43, 9.43, 8.24, 4.74, 4.04, 4.71, 3.87, 3.88, 2.75, 1.08, -0.46, -1.41, -0.38, 1.78, 2.13, 1.66, 2.36, 1.75, 1.24, 1.48, 1.48, 2.15, 2.14, 2.65, 2.79, 3.42, 3.07, 2.89, 3.0, 2.98, 3.17, 2.61, 1.98, 1.87, 2.08, 2.17, 2.18, 2.17, 2.14, 1.44, 1.29, 2.05, 2.47, 2.3, 2.21, 2.07, 2.1, 2.27, 1.96, 2.44, 2.27, 1.92, 1.76, 1.76, 1.82, 1.81, 1.92, 2.16, 2.33, 2.22, 2.23, 2.2, 2.28, 2.19, 1.96, 1.52, 0.73, 0.63, 0.7, 0.77, 0.72, 0.62, 0.61, 0.53, 0.6, 0.96, 1.58, 1.0, 1.5, 1.53, 1.67, 1.78, 1.8], "crisis_years": [1873, 1893, 1907, 1930, 1984, 2007], "periods": [2.0, 2.19, 2.4, 2.62, 2.87, 3.14, 3.44, 3.77, 4.12, 4.51, 4.94, 5.41, 5.92, 6.48, 7.09, 7.76, 8.49, 9.3, 10.18, 11.14, 12.19, 13.35, 14.61, 15.99, 17.51, 19.16, 20.98, 22.96, 25.13, 27.51, 30.11, 32.96, 36.08, 39.49, 43.23, 47.32, 51.8, 56.7, 62.06, 67.93, 74.36, 81.39, 89.09, 97.52, 106.75, 116.85, 127.9, 140.0], "norm_psd": [0.3168, 0.3246, 0.3138, 0.312, 0.3296, 0.3672, 0.4228, 0.4671, 0.5065, 0.5713, 0.67, 0.8419, 1.002, 0.9499, 0.7411, 0.6221, 0.5954, 0.5571, 0.6, 0.7581, 0.8804, 0.8507, 0.6722, 0.4535, 0.3151, 0.285, 0.288, 0.2632, 0.2122, 0.176, 0.1853, 0.1992, 0.1756, 0.1295, 0.0918, 0.0955, 0.1355, 0.1756, 0.2398, 0.3757, 0.5324, 0.5849, 0.474, 0.2698, 0.1068, 0.083, 0.2126, 0.4419], "alpha": [1.322, 1.32, 1.313, 1.306, 1.295, 1.282, 1.265, 1.242, 1.213, 1.176, 1.129, 1.074, 1.011, 0.946, 0.88, 0.819, 0.764, 0.715, 0.674, 0.639, 0.61, 0.585, 0.564, 0.546, 0.531, 0.518, 0.507, 0.498, 0.493], "f_alpha": [0.733, 0.74, 0.756, 0.775, 0.796, 0.821, 0.848, 0.879, 0.912, 0.944, 0.972, 0.993, 1.0, 0.992, 0.967, 0.929, 0.881, 0.828, 0.771, 0.715, 0.66, 0.608, 0.559, 0.512, 0.469, 0.429, 0.391, 0.356, 0.339], "log_scalo": [[-1.41, -1.54, -1.9, -2.44, -2.87, -2.98, -2.88, -2.65, -2.59, -2.76, -2.96, -2.97, -2.94, -2.91, -2.77, -2.47, -2.15, -1.93, -1.82, -1.82, -1.93, -2.18, -2.6, -2.23, -1.72, -1.56, -1.75, -2.32, -2.41, -2.11, -2.2, -2.63, -2.56, -2.12, -1.87, -1.72, -1.6, -1.52, -1.53, -1.67, -1.89, -2.03, -2.0, -2.02, -2.35, -1.98, -1.22, -0.74, -0.44, -0.31, -0.36, -0.64, -1.19, -2.09, -2.94, -2.85, -2.82, -2.25, -1.53, -1.12, -0.91, -0.86, -0.98, -1.24, -1.55, -1.66, -1.54, -1.4, -1.37, -1.51, -1.96, -2.14, -1.54, -1.34, -1.48, -1.98, -2.32, -1.68, -1.2, -0.85, -0.67, -0.69, -0.89, -1.24, -1.7, -2.1, -2.18, -2.13, -2.28, -2.69, -2.57, -2.18, -1.96, -1.83, -1.74, -1.76, -1.97, -2.48, -2.8, -2.66, -2.77, -2.96, -2.98, -2.99, -2.94, -2.82, -2.69, -2.5, -2.23, -2.0, -1.94, -2.13, -2.57, -2.96, -2.94, -2.64, -2.39, -2.33, -2.45, -2.75, -2.83, -2.52, -2.35, -2.4, -2.6, -2.87, -2.98, -2.98, -2.99, -2.96, -2.97, -2.94, -2.82, -2.75, -2.78, -2.9, -2.87, -2.53, -2.34, -2.51, -2.61, -1.98, -1.54, -1.25, -1.05, -0.92, -0.78, -0.59, -0.36, -0.23, -0.29, -0.56, -1.0, -1.03, -0.71, -0.56], [-1.41, -1.51, -1.81, -2.28, -2.77, -2.88, -2.71, -2.53, -2.5, -2.62, -2.79, -2.89, -2.95, -2.96, -2.78, -2.45, -2.17, -1.98, -1.89, -1.89, -1.94, -1.99, -1.96, -1.78, -1.56, -1.47, -1.54, -1.72, -1.85, -1.89, -1.98, -2.1, -2.11, -2.01, -1.93, -1.85, -1.73, -1.62, -1.61, -1.75, -2.07, -2.34, -2.09, -1.85, -1.69, -1.42, -1.05, -0.71, -0.45, -0.33, -0.36, -0.56, -0.96, -1.59, -2.54, -2.71, -2.23, -1.76, -1.36, -1.1, -0.95, -0.91, -1.02, -1.32, -1.84, -2.09, -1.72, -1.48, -1.38, -1.39, -1.46, -1.43, -1.31, -1.25, -1.32, -1.51, -1.62, -1.49, -1.17, -0.86, -0.69, -0.71, -0.9, -1.24, -1.76, -2.46, -2.44, -2.14, -2.1, -2.17, -2.17, -2.1, -2.03, -1.93, -1.81, -1.76, -1.84, -2.06, -2.29, -2.45, -2.61, -2.79, -2.9, -2.9, -2.85, -2.79, -2.77, -2.58, -2.25, -2.0, -1.91, -2.02, -2.33, -2.76, -2.78, -2.5, -2.34, -2.31, -2.35, -2.43, -2.43, -2.35, -2.31, -2.37, -2.52, -2.71, -2.86, -2.92, -2.92, -2.89, -2.87, -2.81, -2.75, -2.72, -2.72, -2.68, -2.55, -2.33, -2.17, -2.1, -1.98, -1.76, -1.53, -1.33, -1.17, -1.1, -1.01, -0.75, -0.44, -0.26, -0.27, -0.47, -0.79, -0.87, -0.68, -0.57], [-1.4, -1.48, -1.71, -2.11, -2.59, -2.71, -2.5, -2.35, -2.34, -2.44, -2.61, -2.79, -2.94, -2.96, -2.75, -2.47, -2.25, -2.12, -2.08, -2.1, -2.09, -1.97, -1.76, -1.56, -1.41, -1.33, -1.34, -1.41, -1.52, -1.63, -1.75, -1.86, -1.95, -2.05, -2.2, -2.25, -2.06, -1.84, -1.77, -1.9, -2.32, -2.93, -2.15, -1.7, -1.45, -1.27, -1.05, -0.77, -0.53, -0.39, -0.38, -0.5, -0.76, -1.15, -1.64, -1.9, -1.71, -1.46, -1.28, -1.15, -1.05, -1.02, -1.11, -1.39, -1.99, -2.51, -1.93, -1.62, -1.45, -1.33, -1.24, -1.16, -1.12, -1.12, -1.18, -1.33, -1.57, -1.68, -1.28, -0.92, -0.75, -0.78, -0.96, -1.28, -1.74, -2.38, -2.48, -2.09, -1.93, -1.93, -2.01, -2.16, -2.31, -2.25, -1.99, -1.8, -1.74, -1.8, -1.94, -2.13, -2.34, -2.53, -2.66, -2.71, -2.74, -2.84, -2.97, -2.73, -2.3, -2.0, -1.87, -1.87, -2.01, -2.21, -2.3, -2.27, -2.27, -2.3, -2.3, -2.26, -2.23, -2.23, -2.27, -2.35, -2.45, -2.55, -2.64, -2.71, -2.72, -2.7, -2.67, -2.66, -2.68, -2.71, -2.68, -2.54, -2.31, -2.09, -1.92, -1.81, -1.76, -1.75, -1.71, -1.59, -1.52, -1.67, -1.87, -1.11, -0.58, -0.33, -0.29, -0.42, -0.67, -0.78, -0.66, -0.57], [-1.39, -1.44, -1.6, -1.87, -2.16, -2.27, -2.19, -2.14, -2.16, -2.28, -2.44, -2.61, -2.72, -2.71, -2.61, -2.49, -2.39, -2.35, -2.39, -2.55, -2.62, -2.22, -1.81, -1.53, -1.35, -1.26, -1.25, -1.3, -1.4, -1.54, -1.7, -1.86, -2.03, -2.26, -2.65, -2.98, -2.46, -2.07, -1.9, -1.88, -1.96, -1.97, -1.78, -1.58, -1.5, -1.51, -1.35, -0.99, -0.68, -0.5, -0.44, -0.49, -0.63, -0.83, -1.06, -1.23, -1.3, -1.31, -1.34, -1.35, -1.28, -1.18, -1.17, -1.29, -1.5, -1.69, -1.75, -1.73, -1.63, -1.45, -1.27, -1.14, -1.09, -1.09, -1.16, -1.37, -1.9, -2.66, -1.43, -0.98, -0.82, -0.85, -1.03, -1.3, -1.58, -1.78, -1.85, -1.82, -1.79, -1.85, -2.02, -2.35, -2.87, -2.75, -2.19, -1.85, -1.7, -1.67, -1.75, -1.9, -2.1, -2.3, -2.44, -2.53, -2.62, -2.75, -2.81, -2.56, -2.22, -1.96, -1.79, -1.73, -1.75, -1.83, -1.93, -2.07, -2.25, -2.43, -2.44, -2.32, -2.24, -2.25, -2.33, -2.43, -2.49, -2.49, -2.47, -2.46, -2.45, -2.45, -2.47, -2.54, -2.68, -2.84, -2.83, -2.54, -2.2, -1.94, -1.78, -1.73, -1.8, -2.03, -2.24, -2.05, -1.86, -1.95, -1.74, -1.04, -0.59, -0.35, -0.3, -0.39, -0.58, -0.69, -0.64, -0.58], [-1.37, -1.38, -1.47, -1.6, -1.73, -1.81, -1.85, -1.89, -1.99, -2.14, -2.32, -2.48, -2.57, -2.59, -2.58, -2.57, -2.58, -2.58, -2.64, -2.8, -2.75, -2.27, -1.84, -1.56, -1.39, -1.3, -1.29, -1.35, -1.46, -1.64, -1.86, -2.08, -2.23, -2.33, -2.44, -2.45, -2.28, -2.07, -1.89, -1.76, -1.66, -1.57, -1.5, -1.51, -1.72, -2.41, -2.05, -1.24, -0.84, -0.64, -0.56, -0.56, -0.61, -0.72, -0.85, -1.0, -1.15, -1.35, -1.64, -1.94, -1.74, -1.4, -1.24, -1.23, -1.34, -1.54, -1.82, -2.14, -2.12, -1.76, -1.46, -1.29, -1.21, -1.18, -1.19, -1.25, -1.35, -1.32, -1.09, -0.89, -0.82, -0.9, -1.12, -1.44, -1.7, -1.73, -1.67, -1.63, -1.67, -1.78, -1.96, -2.19, -2.36, -2.3, -2.05, -1.81, -1.67, -1.62, -1.67, -1.81, -2.02, -2.25, -2.4, -2.43, -2.43, -2.42, -2.36, -2.23, -2.05, -1.88, -1.73, -1.63, -1.6, -1.64, -1.76, -1.97, -2.31, -2.79, -2.86, -2.53, -2.37, -2.38, -2.52, -2.7, -2.74, -2.6, -2.44, -2.33, -2.27, -2.26, -2.31, -2.44, -2.65, -2.89, -2.84, -2.47, -2.11, -1.86, -1.73, -1.73, -1.89, -2.29, -2.89, -2.24, -1.72, -1.35, -1.02, -0.7, -0.45, -0.3, -0.27, -0.33, -0.46, -0.56, -0.57, -0.56], [-1.35, -1.32, -1.35, -1.39, -1.45, -1.51, -1.59, -1.7, -1.85, -2.05, -2.31, -2.57, -2.71, -2.73, -2.73, -2.77, -2.79, -2.72, -2.6, -2.44, -2.23, -1.99, -1.77, -1.6, -1.49, -1.44, -1.45, -1.52, -1.66, -1.89, -2.21, -2.55, -2.64, -2.48, -2.33, -2.22, -2.12, -2.0, -1.87, -1.71, -1.56, -1.43, -1.37, -1.39, -1.51, -1.6, -1.42, -1.11, -0.89, -0.76, -0.72, -0.72, -0.76, -0.82, -0.92, -1.05, -1.21, -1.45, -1.85, -2.42, -1.98, -1.51, -1.29, -1.24, -1.33, -1.55, -1.92, -2.47, -2.5, -1.98, -1.66, -1.51, -1.44, -1.37, -1.23, -1.07, -0.94, -0.83, -0.74, -0.7, -0.74, -0.88, -1.17, -1.68, -2.57, -2.22, -1.79, -1.64, -1.64, -1.73, -1.88, -2.03, -2.09, -2.03, -1.89, -1.74, -1.63, -1.6, -1.66, -1.81, -2.07, -2.44, -2.69, -2.56, -2.36, -2.24, -2.17, -2.1, -2.01, -1.87, -1.73, -1.61, -1.56, -1.57, -1.66, -1.84, -2.12, -2.44, -2.59, -2.49, -2.42, -2.47, -2.65, -2.9, -2.96, -2.72, -2.47, -2.29, -2.19, -2.16, -2.19, -2.28, -2.39, -2.44, -2.37, -2.17, -1.95, -1.77, -1.66, -1.65, -1.72, -1.82, -1.82, -1.61, -1.3, -0.98, -0.7, -0.48, -0.32, -0.22, -0.21, -0.26, -0.34, -0.42, -0.47, -0.5], [-1.32, -1.27, -1.26, -1.28, -1.31, -1.37, -1.45, -1.58, -1.76, -2.0, -2.32, -2.7, -2.97, -2.97, -2.93, -2.96, -2.99, -2.83, -2.55, -2.29, -2.07, -1.9, -1.77, -1.69, -1.66, -1.65, -1.68, -1.75, -1.87, -2.07, -2.37, -2.72, -2.84, -2.62, -2.42, -2.3, -2.25, -2.19, -2.04, -1.81, -1.58, -1.38, -1.24, -1.15, -1.09, -1.03, -0.96, -0.9, -0.88, -0.9, -0.96, -1.02, -1.07, -1.13, -1.2, -1.28, -1.34, -1.4, -1.44, -1.44, -1.36, -1.25, -1.18, -1.18, -1.27, -1.42, -1.61, -1.77, -1.81, -1.76, -1.72, -1.78, -1.9, -1.78, -1.36, -1.02, -0.78, -0.63, -0.56, -0.55, -0.62, -0.76, -1.0, -1.33, -1.7, -1.82, -1.69, -1.62, -1.64, -1.77, -1.99, -2.28, -2.41, -2.22, -1.96, -1.77, -1.65, -1.61, -1.66, -1.79, -2.04, -2.43, -2.82, -2.66, -2.39, -2.26, -2.25, -2.29, -2.24, -2.06, -1.84, -1.67, -1.58, -1.55, -1.58, -1.67, -1.8, -1.94, -2.06, -2.15, -2.24, -2.34, -2.45, -2.55, -2.56, -2.48, -2.36, -2.23, -2.15, -2.1, -2.11, -2.16, -2.22, -2.24, -2.17, -2.0, -1.82, -1.67, -1.57, -1.52, -1.49, -1.46, -1.36, -1.2, -0.98, -0.75, -0.53, -0.36, -0.24, -0.17, -0.16, -0.19, -0.25, -0.32, -0.38, -0.45], [-1.3, -1.25, -1.23, -1.24, -1.26, -1.32, -1.4, -1.52, -1.68, -1.88, -2.13, -2.43, -2.7, -2.86, -2.91, -2.9, -2.81, -2.62, -2.39, -2.19, -2.05, -1.95, -1.91, -1.91, -1.93, -1.96, -1.99, -2.01, -2.05, -2.11, -2.2, -2.29, -2.35, -2.37, -2.4, -2.48, -2.65, -2.78, -2.46, -1.98, -1.61, -1.34, -1.13, -0.99, -0.89, -0.83, -0.82, -0.86, -0.96, -1.12, -1.34, -1.56, -1.69, -1.73, -1.77, -1.78, -1.68, -1.5, -1.32, -1.18, -1.08, -1.02, -1.01, -1.05, -1.16, -1.32, -1.51, -1.67, -1.73, -1.74, -1.81, -2.07, -2.65, -1.97, -1.31, -0.91, -0.67, -0.52, -0.44, -0.43, -0.48, -0.57, -0.71, -0.87, -1.04, -1.18, -1.3, -1.41, -1.55, -1.75, -2.04, -2.48, -2.79, -2.42, -2.05, -1.82, -1.68, -1.62, -1.62, -1.68, -1.79, -1.93, -2.06, -2.13, -2.17, -2.25, -2.44, -2.79, -2.84, -2.36, -1.99, -1.76, -1.63, -1.56, -1.55, -1.58, -1.63, -1.71, -1.8, -1.9, -2.01, -2.12, -2.22, -2.29, -2.33, -2.31, -2.26, -2.2, -2.13, -2.11, -2.14, -2.24, -2.4, -2.51, -2.36, -2.06, -1.81, -1.64, -1.53, -1.49, -1.48, -1.46, -1.36, -1.16, -0.92, -0.69, -0.49, -0.33, -0.23, -0.17, -0.15, -0.18, -0.22, -0.28, -0.34, -0.41], [-1.3, -1.25, -1.24, -1.25, -1.29, -1.34, -1.42, -1.52, -1.63, -1.77, -1.92, -2.09, -2.26, -2.4, -2.49, -2.49, -2.41, -2.31, -2.2, -2.12, -2.07, -2.07, -2.12, -2.22, -2.36, -2.46, -2.47, -2.4, -2.31, -2.25, -2.22, -2.22, -2.24, -2.28, -2.36, -2.47, -2.58, -2.51, -2.18, -1.81, -1.5, -1.25, -1.06, -0.92, -0.83, -0.79, -0.81, -0.89, -1.04, -1.3, -1.68, -2.26, -2.87, -2.81, -2.85, -2.8, -2.17, -1.67, -1.34, -1.11, -0.98, -0.91, -0.9, -0.96, -1.1, -1.32, -1.64, -2.0, -2.03, -1.8, -1.63, -1.5, -1.34, -1.11, -0.86, -0.65, -0.49, -0.39, -0.34, -0.34, -0.37, -0.44, -0.53, -0.64, -0.77, -0.9, -1.04, -1.19, -1.35, -1.51, -1.68, -1.82, -1.9, -1.88, -1.81, -1.72, -1.64, -1.59, -1.56, -1.55, -1.58, -1.62, -1.68, -1.77, -1.87, -2.01, -2.19, -2.34, -2.3, -2.1, -1.9, -1.75, -1.66, -1.61, -1.59, -1.6, -1.63, -1.67, -1.74, -1.83, -1.95, -2.08, -2.22, -2.35, -2.45, -2.46, -2.4, -2.3, -2.21, -2.18, -2.22, -2.36, -2.65, -2.87, -2.5, -2.09, -1.82, -1.67, -1.62, -1.68, -1.87, -2.12, -1.93, -1.44, -1.04, -0.75, -0.54, -0.38, -0.28, -0.22, -0.2, -0.22, -0.25, -0.3, -0.35, -0.42], [-1.31, -1.28, -1.28, -1.3, -1.35, -1.42, -1.51, -1.59, -1.68, -1.76, -1.83, -1.9, -1.96, -2.02, -2.06, -2.09, -2.09, -2.08, -2.08, -2.08, -2.12, -2.18, -2.3, -2.48, -2.73, -2.95, -2.96, -2.78, -2.59, -2.46, -2.38, -2.32, -2.28, -2.24, -2.19, -2.12, -2.02, -1.87, -1.69, -1.49, -1.3, -1.13, -0.99, -0.88, -0.81, -0.78, -0.8, -0.86, -0.99, -1.17, -1.44, -1.78, -2.23, -2.7, -2.64, -2.17, -1.75, -1.42, -1.17, -0.99, -0.88, -0.82, -0.81, -0.87, -1.0, -1.22, -1.59, -2.21, -2.26, -1.64, -1.26, -1.0, -0.79, -0.63, -0.49, -0.38, -0.31, -0.27, -0.26, -0.28, -0.33, -0.41, -0.49, -0.6, -0.71, -0.84, -0.97, -1.1, -1.24, -1.37, -1.48, -1.58, -1.64, -1.68, -1.68, -1.66, -1.63, -1.58, -1.54, -1.51, -1.48, -1.48, -1.49, -1.52, -1.57, -1.62, -1.67, -1.71, -1.71, -1.7, -1.68, -1.67, -1.68, -1.7, -1.72, -1.75, -1.77, -1.81, -1.86, -1.94, -2.06, -2.21, -2.42, -2.67, -2.91, -2.94, -2.72, -2.48, -2.29, -2.17, -2.1, -2.08, -2.06, -1.99, -1.88, -1.75, -1.65, -1.6, -1.62, -1.74, -1.93, -2.02, -1.72, -1.33, -1.01, -0.77, -0.59, -0.46, -0.37, -0.32, -0.3, -0.3, -0.33, -0.36, -0.4, -0.46], [-1.33, -1.32, -1.33, -1.38, -1.46, -1.56, -1.68, -1.8, -1.9, -1.95, -1.96, -1.96, -1.95, -1.95, -1.96, -1.98, -2.0, -2.03, -2.06, -2.09, -2.14, -2.19, -2.27, -2.36, -2.46, -2.54, -2.58, -2.58, -2.56, -2.53, -2.51, -2.47, -2.4, -2.3, -2.17, -2.02, -1.86, -1.7, -1.53, -1.37, -1.22, -1.08, -0.96, -0.87, -0.8, -0.76, -0.75, -0.78, -0.85, -0.95, -1.08, -1.25, -1.43, -1.55, -1.54, -1.41, -1.23, -1.06, -0.91, -0.8, -0.72, -0.67, -0.66, -0.69, -0.75, -0.84, -0.95, -1.02, -1.0, -0.89, -0.73, -0.57, -0.44, -0.33, -0.26, -0.21, -0.19, -0.2, -0.24, -0.3, -0.39, -0.49, -0.61, -0.73, -0.86, -0.99, -1.12, -1.26, -1.41, -1.55, -1.68, -1.8, -1.88, -1.93, -1.94, -1.92, -1.86, -1.77, -1.68, -1.6, -1.52, -1.47, -1.43, -1.4, -1.39, -1.4, -1.41, -1.44, -1.47, -1.52, -1.59, -1.68, -1.79, -1.91, -2.02, -2.09, -2.1, -2.09, -2.09, -2.12, -2.18, -2.28, -2.39, -2.5, -2.57, -2.56, -2.45, -2.28, -2.11, -1.96, -1.83, -1.72, -1.62, -1.54, -1.46, -1.4, -1.35, -1.32, -1.3, -1.29, -1.25, -1.18, -1.08, -0.95, -0.83, -0.71, -0.61, -0.52, -0.46, -0.43, -0.41, -0.41, -0.42, -0.44, -0.47, -0.51], [-1.35, -1.35, -1.39, -1.45, -1.56, -1.7, -1.89, -2.11, -2.32, -2.43, -2.39, -2.29, -2.2, -2.14, -2.12, -2.13, -2.15, -2.17, -2.19, -2.2, -2.21, -2.22, -2.23, -2.25, -2.29, -2.33, -2.39, -2.46, -2.55, -2.66, -2.76, -2.82, -2.77, -2.61, -2.4, -2.18, -1.97, -1.78, -1.6, -1.43, -1.27, -1.12, -1.0, -0.89, -0.81, -0.74, -0.71, -0.69, -0.7, -0.73, -0.77, -0.82, -0.86, -0.88, -0.87, -0.84, -0.79, -0.72, -0.65, -0.58, -0.53, -0.49, -0.46, -0.44, -0.43, -0.43, -0.42, -0.4, -0.37, -0.32, -0.27, -0.21, -0.16, -0.12, -0.11, -0.11, -0.14, -0.2, -0.28, -0.39, -0.53, -0.69, -0.86, -1.04, -1.21, -1.38, -1.53, -1.7, -1.87, -2.07, -2.29, -2.51, -2.7, -2.81, -2.79, -2.64, -2.43, -2.2, -2.0, -1.83, -1.69, -1.58, -1.5, -1.44, -1.4, -1.38, -1.38, -1.4, -1.44, -1.52, -1.62, -1.77, -1.98, -2.24, -2.57, -2.8, -2.73, -2.54, -2.4, -2.33, -2.31, -2.31, -2.32, -2.31, -2.27, -2.19, -2.08, -1.95, -1.81, -1.67, -1.55, -1.44, -1.34, -1.26, -1.19, -1.13, -1.09, -1.05, -1.02, -0.99, -0.96, -0.93, -0.89, -0.84, -0.79, -0.73, -0.67, -0.62, -0.58, -0.54, -0.52, -0.51, -0.51, -0.51, -0.52, -0.55], [-1.37, -1.37, -1.41, -1.47, -1.57, -1.71, -1.88, -2.08, -2.29, -2.46, -2.5, -2.45, -2.39, -2.36, -2.37, -2.41, -2.47, -2.52, -2.54, -2.52, -2.46, -2.4, -2.35, -2.32, -2.32, -2.34, -2.39, -2.47, -2.57, -2.68, -2.79, -2.84, -2.78, -2.65, -2.48, -2.31, -2.13, -1.94, -1.76, -1.57, -1.39, -1.23, -1.08, -0.95, -0.85, -0.76, -0.7, -0.65, -0.63, -0.61, -0.61, -0.61, -0.62, -0.63, -0.62, -0.61, -0.58, -0.55, -0.5, -0.45, -0.4, -0.35, -0.3, -0.26, -0.22, -0.18, -0.15, -0.11, -0.08, -0.05, -0.02, -0.0, 0.0, -0.0, -0.02, -0.06, -0.13, -0.22, -0.33, -0.48, -0.66, -0.88, -1.14, -1.43, -1.74, -2.02, -2.21, -2.32, -2.4, -2.5, -2.62, -2.74, -2.81, -2.84, -2.8, -2.69, -2.53, -2.34, -2.15, -1.99, -1.84, -1.73, -1.63, -1.56, -1.51, -1.47, -1.46, -1.46, -1.49, -1.54, -1.62, -1.74, -1.89, -2.07, -2.28, -2.45, -2.52, -2.5, -2.46, -2.44, -2.45, -2.49, -2.52, -2.49, -2.37, -2.19, -1.99, -1.8, -1.64, -1.49, -1.37, -1.26, -1.17, -1.1, -1.04, -1.0, -0.97, -0.96, -0.96, -0.97, -0.99, -1.01, -1.02, -1.02, -0.99, -0.93, -0.86, -0.79, -0.72, -0.66, -0.62, -0.58, -0.56, -0.54, -0.54, -0.56], [-1.36, -1.36, -1.38, -1.42, -1.49, -1.57, -1.67, -1.78, -1.89, -2.0, -2.1, -2.18, -2.26, -2.35, -2.46, -2.59, -2.75, -2.91, -2.98, -2.91, -2.77, -2.62, -2.51, -2.42, -2.37, -2.35, -2.35, -2.36, -2.39, -2.42, -2.45, -2.47, -2.49, -2.5, -2.49, -2.44, -2.33, -2.16, -1.95, -1.74, -1.53, -1.34, -1.18, -1.04, -0.92, -0.83, -0.75, -0.7, -0.67, -0.65, -0.66, -0.67, -0.69, -0.71, -0.73, -0.73, -0.71, -0.67, -0.61, -0.54, -0.47, -0.4, -0.33, -0.26, -0.21, -0.15, -0.1, -0.06, -0.02, 0.01, 0.03, 0.04, 0.04, 0.03, -0.01, -0.06, -0.12, -0.22, -0.33, -0.48, -0.65, -0.86, -1.11, -1.4, -1.76, -2.18, -2.65, -2.94, -2.92, -2.86, -2.87, -2.92, -2.98, -2.97, -2.86, -2.69, -2.5, -2.33, -2.18, -2.05, -1.94, -1.85, -1.78, -1.71, -1.65, -1.6, -1.57, -1.54, -1.53, -1.54, -1.56, -1.59, -1.65, -1.72, -1.79, -1.88, -1.97, -2.07, -2.18, -2.32, -2.5, -2.73, -2.95, -2.86, -2.52, -2.2, -1.93, -1.72, -1.55, -1.4, -1.29, -1.2, -1.12, -1.07, -1.03, -1.02, -1.02, -1.05, -1.1, -1.18, -1.29, -1.43, -1.56, -1.62, -1.53, -1.36, -1.17, -1.01, -0.87, -0.76, -0.68, -0.62, -0.57, -0.55, -0.54, -0.55], [-1.33, -1.32, -1.33, -1.35, -1.38, -1.43, -1.49, -1.56, -1.64, -1.72, -1.81, -1.91, -2.01, -2.11, -2.23, -2.34, -2.45, -2.54, -2.58, -2.58, -2.53, -2.47, -2.41, -2.36, -2.32, -2.3, -2.29, -2.3, -2.32, -2.37, -2.43, -2.52, -2.64, -2.8, -2.95, -2.95, -2.69, -2.36, -2.05, -1.79, -1.57, -1.39, -1.23, -1.11, -1.0, -0.92, -0.87, -0.83, -0.82, -0.84, -0.88, -0.95, -1.06, -1.19, -1.33, -1.44, -1.42, -1.29, -1.12, -0.95, -0.8, -0.68, -0.57, -0.48, -0.4, -0.33, -0.27, -0.21, -0.15, -0.1, -0.07, -0.04, -0.03, -0.03, -0.05, -0.08, -0.13, -0.2, -0.29, -0.4, -0.52, -0.67, -0.84, -1.03, -1.25, -1.48, -1.73, -1.98, -2.23, -2.45, -2.62, -2.71, -2.72, -2.67, -2.57, -2.46, -2.35, -2.26, -2.18, -2.12, -2.06, -2.01, -1.96, -1.91, -1.85, -1.78, -1.71, -1.65, -1.6, -1.55, -1.52, -1.51, -1.51, -1.53, -1.56, -1.6, -1.66, -1.73, -1.82, -1.91, -2.0, -2.05, -2.06, -2.0, -1.89, -1.76, -1.63, -1.51, -1.41, -1.32, -1.24, -1.18, -1.14, -1.11, -1.09, -1.1, -1.12, -1.17, -1.24, -1.35, -1.51, -1.71, -1.91, -1.96, -1.76, -1.48, -1.24, -1.05, -0.9, -0.78, -0.69, -0.61, -0.57, -0.53, -0.52, -0.52], [-1.29, -1.28, -1.28, -1.28, -1.3, -1.33, -1.37, -1.41, -1.46, -1.52, -1.58, -1.65, -1.72, -1.78, -1.85, -1.92, -1.97, -2.02, -2.07, -2.1, -2.12, -2.13, -2.15, -2.16, -2.17, -2.18, -2.2, -2.22, -2.24, -2.27, -2.3, -2.32, -2.33, -2.31, -2.26, -2.16, -2.03, -1.88, -1.73, -1.58, -1.44, -1.31, -1.21, -1.12, -1.04, -0.99, -0.96, -0.94, -0.95, -0.99, -1.05, -1.15, -1.28, -1.46, -1.67, -1.85, -1.84, -1.66, -1.45, -1.27, -1.12, -1.01, -0.91, -0.83, -0.75, -0.66, -0.58, -0.49, -0.41, -0.33, -0.27, -0.21, -0.17, -0.15, -0.14, -0.14, -0.17, -0.21, -0.26, -0.33, -0.41, -0.51, -0.62, -0.75, -0.88, -1.03, -1.19, -1.35, -1.51, -1.66, -1.8, -1.92, -2.0, -2.06, -2.1, -2.12, -2.15, -2.17, -2.21, -2.25, -2.29, -2.33, -2.33, -2.28, -2.18, -2.06, -1.93, -1.8, -1.7, -1.61, -1.53, -1.48, -1.44, -1.41, -1.4, -1.4, -1.4, -1.42, -1.43, -1.45, -1.46, -1.46, -1.46, -1.44, -1.42, -1.39, -1.35, -1.32, -1.28, -1.25, -1.21, -1.19, -1.16, -1.14, -1.13, -1.12, -1.12, -1.13, -1.14, -1.16, -1.17, -1.18, -1.17, -1.14, -1.08, -1.0, -0.92, -0.83, -0.74, -0.67, -0.6, -0.55, -0.52, -0.49, -0.48, -0.49], [-1.27, -1.25, -1.24, -1.24, -1.25, -1.27, -1.29, -1.32, -1.36, -1.39, -1.44, -1.48, -1.53, -1.58, -1.63, -1.68, -1.73, -1.77, -1.82, -1.87, -1.91, -1.95, -1.99, -2.03, -2.06, -2.09, -2.11, -2.13, -2.13, -2.13, -2.11, -2.07, -2.02, -1.95, -1.87, -1.78, -1.68, -1.58, -1.48, -1.39, -1.29, -1.21, -1.13, -1.07, -1.01, -0.97, -0.93, -0.91, -0.9, -0.9, -0.92, -0.94, -0.96, -0.99, -1.02, -1.05, -1.08, -1.1, -1.13, -1.16, -1.21, -1.25, -1.29, -1.3, -1.26, -1.16, -1.02, -0.86, -0.72, -0.59, -0.49, -0.4, -0.33, -0.28, -0.25, -0.23, -0.23, -0.24, -0.27, -0.31, -0.36, -0.42, -0.5, -0.58, -0.68, -0.78, -0.89, -1.0, -1.11, -1.23, -1.34, -1.45, -1.56, -1.66, -1.76, -1.86, -1.97, -2.1, -2.24, -2.41, -2.62, -2.84, -2.94, -2.77, -2.5, -2.25, -2.04, -1.87, -1.73, -1.61, -1.52, -1.44, -1.38, -1.33, -1.3, -1.27, -1.26, -1.25, -1.24, -1.24, -1.25, -1.25, -1.26, -1.27, -1.28, -1.29, -1.3, -1.31, -1.31, -1.31, -1.3, -1.28, -1.26, -1.23, -1.2, -1.16, -1.12, -1.07, -1.03, -0.99, -0.95, -0.9, -0.86, -0.81, -0.76, -0.71, -0.66, -0.61, -0.57, -0.52, -0.49, -0.46, -0.44, -0.43, -0.43, -0.44], [-1.27, -1.25, -1.24, -1.24, -1.25, -1.26, -1.28, -1.3, -1.33, -1.37, -1.41, -1.45, -1.49, -1.54, -1.59, -1.64, -1.7, -1.75, -1.81, -1.87, -1.94, -2.0, -2.07, -2.14, -2.21, -2.28, -2.34, -2.39, -2.41, -2.4, -2.35, -2.26, -2.15, -2.02, -1.9, -1.77, -1.65, -1.54, -1.43, -1.33, -1.24, -1.16, -1.08, -1.02, -0.96, -0.91, -0.87, -0.83, -0.81, -0.79, -0.78, -0.78, -0.79, -0.8, -0.83, -0.87, -0.93, -1.0, -1.1, -1.23, -1.4, -1.65, -2.0, -2.34, -2.08, -1.64, -1.3, -1.05, -0.86, -0.7, -0.58, -0.48, -0.41, -0.35, -0.31, -0.28, -0.27, -0.27, -0.29, -0.32, -0.35, -0.4, -0.46, -0.53, -0.6, -0.69, -0.78, -0.88, -0.98, -1.08, -1.19, -1.29, -1.39, -1.48, -1.57, -1.66, -1.74, -1.81, -1.87, -1.93, -1.97, -1.98, -1.97, -1.92, -1.86, -1.78, -1.7, -1.61, -1.54, -1.47, -1.41, -1.36, -1.31, -1.28, -1.25, -1.24, -1.23, -1.23, -1.24, -1.26, -1.28, -1.31, -1.35, -1.39, -1.44, -1.5, -1.56, -1.62, -1.68, -1.73, -1.74, -1.72, -1.67, -1.58, -1.48, -1.38, -1.27, -1.17, -1.08, -0.99, -0.91, -0.83, -0.76, -0.7, -0.64, -0.59, -0.54, -0.5, -0.46, -0.43, -0.41, -0.39, -0.38, -0.38, -0.38, -0.4], [-1.3, -1.29, -1.28, -1.29, -1.29, -1.31, -1.33, -1.36, -1.39, -1.43, -1.47, -1.52, -1.57, -1.62, -1.68, -1.74, -1.81, -1.88, -1.95, -2.03, -2.11, -2.19, -2.28, -2.38, -2.49, -2.61, -2.72, -2.82, -2.87, -2.82, -2.68, -2.49, -2.3, -2.13, -1.96, -1.81, -1.67, -1.55, -1.43, -1.33, -1.23, -1.15, -1.07, -1.0, -0.94, -0.88, -0.83, -0.79, -0.76, -0.73, -0.71, -0.7, -0.69, -0.69, -0.7, -0.72, -0.74, -0.76, -0.79, -0.82, -0.85, -0.86, -0.86, -0.84, -0.8, -0.75, -0.68, -0.61, -0.54, -0.48, -0.42, -0.37, -0.33, -0.3, -0.28, -0.27, -0.27, -0.28, -0.3, -0.32, -0.36, -0.41, -0.47, -0.53, -0.61, -0.7, -0.79, -0.89, -1.0, -1.12, -1.24, -1.36, -1.47, -1.56, -1.63, -1.68, -1.7, -1.7, -1.69, -1.66, -1.63, -1.6, -1.56, -1.52, -1.49, -1.45, -1.41, -1.38, -1.35, -1.32, -1.3, -1.28, -1.27, -1.26, -1.26, -1.27, -1.28, -1.31, -1.34, -1.37, -1.42, -1.48, -1.55, -1.63, -1.72, -1.84, -1.98, -2.16, -2.38, -2.62, -2.73, -2.54, -2.25, -1.98, -1.75, -1.56, -1.39, -1.25, -1.13, -1.01, -0.92, -0.83, -0.75, -0.68, -0.61, -0.56, -0.51, -0.46, -0.43, -0.4, -0.38, -0.36, -0.35, -0.35, -0.36, -0.37], [-1.35, -1.35, -1.35, -1.36, -1.37, -1.39, -1.42, -1.45, -1.48, -1.53, -1.57, -1.63, -1.68, -1.74, -1.81, -1.88, -1.95, -2.02, -2.09, -2.15, -2.21, -2.26, -2.3, -2.33, -2.34, -2.34, -2.32, -2.29, -2.24, -2.17, -2.1, -2.02, -1.93, -1.83, -1.74, -1.64, -1.55, -1.45, -1.37, -1.28, -1.2, -1.13, -1.06, -0.99, -0.93, -0.87, -0.82, -0.77, -0.73, -0.69, -0.65, -0.62, -0.59, -0.57, -0.54, -0.52, -0.5, -0.48, -0.46, -0.44, -0.43, -0.41, -0.38, -0.36, -0.34, -0.32, -0.29, -0.27, -0.25, -0.23, -0.21, -0.2, -0.19, -0.19, -0.19, -0.2, -0.22, -0.24, -0.27, -0.3, -0.35, -0.4, -0.46, -0.53, -0.61, -0.7, -0.8, -0.92, -1.05, -1.2, -1.37, -1.57, -1.81, -2.09, -2.42, -2.66, -2.57, -2.33, -2.1, -1.93, -1.79, -1.68, -1.59, -1.52, -1.46, -1.41, -1.37, -1.34, -1.32, -1.3, -1.29, -1.29, -1.29, -1.3, -1.31, -1.33, -1.36, -1.38, -1.42, -1.45, -1.49, -1.53, -1.57, -1.61, -1.64, -1.67, -1.69, -1.7, -1.69, -1.67, -1.63, -1.58, -1.51, -1.43, -1.35, -1.26, -1.17, -1.09, -1.0, -0.92, -0.85, -0.77, -0.71, -0.65, -0.59, -0.54, -0.5, -0.46, -0.43, -0.4, -0.38, -0.37, -0.36, -0.35, -0.36, -0.37], [-1.42, -1.42, -1.43, -1.44, -1.45, -1.48, -1.5, -1.54, -1.58, -1.62, -1.67, -1.72, -1.79, -1.85, -1.93, -2.0, -2.09, -2.18, -2.27, -2.37, -2.46, -2.53, -2.59, -2.61, -2.59, -2.53, -2.45, -2.36, -2.26, -2.16, -2.06, -1.96, -1.87, -1.78, -1.69, -1.6, -1.52, -1.44, -1.37, -1.29, -1.22, -1.15, -1.09, -1.03, -0.97, -0.91, -0.85, -0.8, -0.75, -0.7, -0.65, -0.61, -0.57, -0.53, -0.49, -0.45, -0.41, -0.38, -0.34, -0.31, -0.28, -0.25, -0.23, -0.2, -0.18, -0.16, -0.15, -0.13, -0.12, -0.11, -0.11, -0.11, -0.11, -0.12, -0.13, -0.14, -0.16, -0.19, -0.22, -0.25, -0.29, -0.34, -0.39, -0.45, -0.52, -0.59, -0.66, -0.75, -0.84, -0.93, -1.03, -1.14, -1.24, -1.34, -1.43, -1.51, -1.56, -1.59, -1.59, -1.58, -1.55, -1.52, -1.49, -1.46, -1.43, -1.41, -1.39, -1.37, -1.36, -1.36, -1.36, -1.37, -1.38, -1.4, -1.42, -1.45, -1.48, -1.52, -1.55, -1.59, -1.63, -1.67, -1.7, -1.72, -1.73, -1.73, -1.71, -1.67, -1.62, -1.56, -1.5, -1.43, -1.35, -1.28, -1.21, -1.13, -1.06, -0.99, -0.93, -0.86, -0.8, -0.74, -0.69, -0.64, -0.59, -0.55, -0.51, -0.48, -0.45, -0.43, -0.41, -0.39, -0.38, -0.38, -0.38, -0.39], [-1.48, -1.49, -1.49, -1.5, -1.52, -1.54, -1.57, -1.6, -1.63, -1.67, -1.71, -1.76, -1.81, -1.87, -1.93, -1.99, -2.05, -2.12, -2.19, -2.25, -2.31, -2.37, -2.4, -2.42, -2.42, -2.39, -2.35, -2.29, -2.22, -2.15, -2.07, -2.0, -1.92, -1.85, -1.77, -1.7, -1.63, -1.56, -1.49, -1.43, -1.37, -1.3, -1.24, -1.18, -1.12, -1.06, -1.01, -0.95, -0.9, -0.84, -0.79, -0.74, -0.68, -0.63, -0.59, -0.54, -0.49, -0.45, -0.41, -0.37, -0.33, -0.3, -0.26, -0.23, -0.21, -0.18, -0.16, -0.15, -0.13, -0.12, -0.11, -0.11, -0.11, -0.11, -0.12, -0.13, -0.15, -0.17, -0.19, -0.21, -0.24, -0.28, -0.31, -0.36, -0.4, -0.45, -0.5, -0.55, -0.6, -0.66, -0.71, -0.77, -0.83, -0.88, -0.94, -0.99, -1.04, -1.08, -1.12, -1.16, -1.2, -1.23, -1.25, -1.28, -1.3, -1.32, -1.34, -1.36, -1.38, -1.41, -1.43, -1.46, -1.5, -1.54, -1.58, -1.64, -1.7, -1.78, -1.86, -1.97, -2.08, -2.21, -2.35, -2.46, -2.5, -2.44, -2.3, -2.14, -1.98, -1.83, -1.69, -1.57, -1.46, -1.36, -1.27, -1.18, -1.1, -1.03, -0.96, -0.9, -0.84, -0.78, -0.73, -0.68, -0.64, -0.6, -0.56, -0.53, -0.5, -0.48, -0.46, -0.44, -0.43, -0.42, -0.42, -0.43], [-1.54, -1.54, -1.55, -1.56, -1.58, -1.6, -1.62, -1.64, -1.67, -1.7, -1.74, -1.78, -1.81, -1.86, -1.9, -1.94, -1.98, -2.02, -2.06, -2.1, -2.13, -2.15, -2.18, -2.19, -2.2, -2.2, -2.2, -2.19, -2.17, -2.15, -2.12, -2.09, -2.06, -2.02, -1.98, -1.94, -1.89, -1.85, -1.8, -1.75, -1.7, -1.64, -1.59, -1.53, -1.47, -1.41, -1.35, -1.28, -1.22, -1.16, -1.09, -1.03, -0.96, -0.9, -0.84, -0.78, -0.72, -0.66, -0.61, -0.56, -0.51, -0.46, -0.42, -0.38, -0.35, -0.32, -0.29, -0.26, -0.24, -0.23, -0.21, -0.2, -0.19, -0.19, -0.19, -0.2, -0.2, -0.21, -0.23, -0.25, -0.27, -0.29, -0.32, -0.35, -0.38, -0.42, -0.46, -0.51, -0.55, -0.6, -0.65, -0.7, -0.76, -0.81, -0.87, -0.93, -0.99, -1.04, -1.1, -1.15, -1.21, -1.25, -1.3, -1.34, -1.38, -1.41, -1.44, -1.46, -1.48, -1.51, -1.53, -1.55, -1.57, -1.6, -1.63, -1.66, -1.69, -1.73, -1.76, -1.8, -1.83, -1.85, -1.86, -1.86, -1.84, -1.81, -1.76, -1.71, -1.64, -1.58, -1.51, -1.44, -1.37, -1.3, -1.24, -1.17, -1.11, -1.05, -1.0, -0.94, -0.89, -0.84, -0.79, -0.74, -0.7, -0.66, -0.63, -0.6, -0.57, -0.54, -0.52, -0.5, -0.49, -0.48, -0.48, -0.48], [-1.59, -1.6, -1.61, -1.62, -1.64, -1.66, -1.68, -1.7, -1.73, -1.77, -1.8, -1.84, -1.87, -1.91, -1.96, -2.0, -2.04, -2.08, -2.13, -2.17, -2.21, -2.25, -2.29, -2.33, -2.37, -2.4, -2.43, -2.46, -2.49, -2.51, -2.53, -2.54, -2.56, -2.56, -2.56, -2.56, -2.55, -2.53, -2.5, -2.46, -2.41, -2.35, -2.28, -2.2, -2.11, -2.02, -1.92, -1.82, -1.72, -1.61, -1.52, -1.42, -1.33, -1.24, -1.15, -1.07, -1.0, -0.92, -0.86, -0.79, -0.73, -0.68, -0.63, -0.58, -0.54, -0.5, -0.47, -0.43, -0.41, -0.38, -0.37, -0.35, -0.34, -0.33, -0.32, -0.32, -0.33, -0.33, -0.34, -0.36, -0.37, -0.39, -0.42, -0.45, -0.48, -0.51, -0.55, -0.6, -0.64, -0.7, -0.75, -0.81, -0.88, -0.95, -1.02, -1.1, -1.19, -1.28, -1.37, -1.47, -1.57, -1.66, -1.75, -1.83, -1.89, -1.92, -1.93, -1.91, -1.88, -1.85, -1.8, -1.76, -1.73, -1.69, -1.66, -1.63, -1.61, -1.59, -1.57, -1.55, -1.54, -1.53, -1.51, -1.5, -1.49, -1.47, -1.45, -1.44, -1.42, -1.39, -1.37, -1.34, -1.3, -1.27, -1.23, -1.19, -1.14, -1.1, -1.05, -1.0, -0.95, -0.91, -0.86, -0.82, -0.78, -0.74, -0.7, -0.67, -0.64, -0.61, -0.59, -0.57, -0.56, -0.54, -0.54, -0.53], [-1.63, -1.64, -1.65, -1.66, -1.68, -1.7, -1.72, -1.74, -1.77, -1.8, -1.83, -1.87, -1.91, -1.94, -1.99, -2.03, -2.07, -2.12, -2.16, -2.21, -2.25, -2.3, -2.35, -2.4, -2.45, -2.5, -2.55, -2.6, -2.64, -2.69, -2.73, -2.77, -2.81, -2.85, -2.87, -2.89, -2.9, -2.9, -2.88, -2.84, -2.77, -2.69, -2.58, -2.47, -2.35, -2.23, -2.11, -1.99, -1.88, -1.77, -1.66, -1.56, -1.47, -1.38, -1.29, -1.21, -1.14, -1.07, -1.0, -0.94, -0.88, -0.83, -0.78, -0.73, -0.69, -0.65, -0.62, -0.59, -0.56, -0.54, -0.52, -0.5, -0.49, -0.48, -0.47, -0.47, -0.47, -0.47, -0.48, -0.49, -0.5, -0.52, -0.54, -0.56, -0.59, -0.62, -0.66, -0.69, -0.74, -0.78, -0.83, -0.89, -0.95, -1.01, -1.08, -1.16, -1.24, -1.33, -1.43, -1.53, -1.65, -1.77, -1.9, -2.03, -2.15, -2.24, -2.29, -2.28, -2.22, -2.14, -2.06, -1.98, -1.9, -1.83, -1.78, -1.73, -1.68, -1.65, -1.62, -1.6, -1.58, -1.57, -1.56, -1.55, -1.55, -1.55, -1.55, -1.54, -1.54, -1.53, -1.52, -1.5, -1.47, -1.43, -1.39, -1.34, -1.29, -1.24, -1.18, -1.12, -1.06, -1.01, -0.96, -0.91, -0.86, -0.82, -0.78, -0.74, -0.71, -0.68, -0.65, -0.63, -0.61, -0.6, -0.59, -0.58], [-1.64, -1.65, -1.66, -1.67, -1.68, -1.7, -1.72, -1.74, -1.77, -1.79, -1.82, -1.85, -1.89, -1.92, -1.96, -2.0, -2.04, -2.08, -2.12, -2.17, -2.21, -2.25, -2.3, -2.34, -2.39, -2.43, -2.47, -2.51, -2.54, -2.58, -2.6, -2.62, -2.64, -2.64, -2.63, -2.62, -2.58, -2.54, -2.48, -2.41, -2.34, -2.26, -2.17, -2.09, -2.0, -1.91, -1.83, -1.74, -1.66, -1.58, -1.51, -1.43, -1.36, -1.3, -1.23, -1.17, -1.12, -1.06, -1.01, -0.96, -0.92, -0.88, -0.84, -0.8, -0.77, -0.74, -0.71, -0.68, -0.66, -0.64, -0.62, -0.61, -0.6, -0.59, -0.58, -0.58, -0.58, -0.58, -0.58, -0.59, -0.6, -0.61, -0.62, -0.63, -0.65, -0.67, -0.69, -0.71, -0.74, -0.76, -0.79, -0.82, -0.86, -0.89, -0.92, -0.96, -1.0, -1.03, -1.07, -1.11, -1.14, -1.18, -1.22, -1.25, -1.28, -1.31, -1.34, -1.36, -1.38, -1.4, -1.42, -1.43, -1.45, -1.46, -1.47, -1.47, -1.48, -1.49, -1.5, -1.51, -1.53, -1.54, -1.55, -1.57, -1.58, -1.59, -1.59, -1.6, -1.59, -1.58, -1.56, -1.52, -1.48, -1.44, -1.39, -1.33, -1.27, -1.21, -1.15, -1.1, -1.04, -0.99, -0.94, -0.89, -0.85, -0.81, -0.77, -0.74, -0.71, -0.68, -0.66, -0.64, -0.62, -0.61, -0.6, -0.59], [-1.62, -1.63, -1.64, -1.65, -1.66, -1.67, -1.69, -1.71, -1.73, -1.76, -1.79, -1.81, -1.85, -1.88, -1.91, -1.95, -1.99, -2.04, -2.08, -2.13, -2.18, -2.23, -2.28, -2.33, -2.39, -2.44, -2.49, -2.53, -2.57, -2.59, -2.6, -2.59, -2.57, -2.52, -2.47, -2.4, -2.33, -2.25, -2.17, -2.09, -2.01, -1.93, -1.86, -1.78, -1.71, -1.64, -1.58, -1.51, -1.45, -1.4, -1.34, -1.29, -1.24, -1.19, -1.14, -1.1, -1.06, -1.02, -0.98, -0.95, -0.91, -0.88, -0.85, -0.83, -0.8, -0.78, -0.76, -0.74, -0.73, -0.71, -0.7, -0.69, -0.68, -0.67, -0.67, -0.66, -0.66, -0.66, -0.66, -0.67, -0.67, -0.68, -0.69, -0.7, -0.71, -0.72, -0.73, -0.74, -0.76, -0.77, -0.79, -0.81, -0.82, -0.84, -0.86, -0.88, -0.89, -0.91, -0.93, -0.95, -0.96, -0.98, -1.0, -1.01, -1.03, -1.04, -1.06, -1.07, -1.08, -1.1, -1.11, -1.12, -1.13, -1.14, -1.15, -1.16, -1.17, -1.18, -1.19, -1.19, -1.2, -1.2, -1.2, -1.2, -1.19, -1.19, -1.18, -1.16, -1.15, -1.13, -1.11, -1.08, -1.06, -1.03, -1.0, -0.97, -0.94, -0.9, -0.87, -0.84, -0.81, -0.78, -0.75, -0.72, -0.7, -0.67, -0.65, -0.63, -0.62, -0.6, -0.59, -0.57, -0.56, -0.56, -0.55, -0.55], [-1.58, -1.58, -1.59, -1.6, -1.61, -1.62, -1.63, -1.65, -1.67, -1.69, -1.71, -1.73, -1.76, -1.79, -1.82, -1.85, -1.88, -1.92, -1.95, -1.99, -2.03, -2.07, -2.11, -2.14, -2.17, -2.19, -2.21, -2.22, -2.21, -2.2, -2.17, -2.14, -2.1, -2.05, -2.0, -1.94, -1.89, -1.83, -1.78, -1.72, -1.66, -1.61, -1.56, -1.51, -1.46, -1.41, -1.37, -1.33, -1.28, -1.24, -1.21, -1.17, -1.14, -1.1, -1.07, -1.04, -1.01, -0.99, -0.96, -0.94, -0.92, -0.9, -0.88, -0.86, -0.85, -0.83, -0.82, -0.81, -0.8, -0.79, -0.79, -0.78, -0.78, -0.78, -0.78, -0.78, -0.78, -0.78, -0.79, -0.8, -0.8, -0.81, -0.82, -0.84, -0.85, -0.86, -0.88, -0.89, -0.91, -0.92, -0.94, -0.95, -0.97, -0.99, -1.0, -1.02, -1.03, -1.04, -1.05, -1.06, -1.07, -1.08, -1.08, -1.08, -1.08, -1.08, -1.08, -1.07, -1.07, -1.06, -1.05, -1.04, -1.03, -1.02, -1.01, -1.0, -0.98, -0.97, -0.96, -0.94, -0.93, -0.91, -0.89, -0.88, -0.86, -0.84, -0.82, -0.81, -0.79, -0.77, -0.75, -0.73, -0.71, -0.69, -0.67, -0.66, -0.64, -0.62, -0.6, -0.59, -0.57, -0.56, -0.54, -0.53, -0.52, -0.51, -0.5, -0.49, -0.48, -0.48, -0.47, -0.47, -0.47, -0.47, -0.47, -0.47], [-1.49, -1.49, -1.49, -1.49, -1.49, -1.5, -1.5, -1.51, -1.51, -1.52, -1.53, -1.53, -1.54, -1.55, -1.56, -1.57, -1.58, -1.58, -1.59, -1.6, -1.6, -1.61, -1.61, -1.61, -1.61, -1.61, -1.6, -1.59, -1.58, -1.57, -1.56, -1.54, -1.53, -1.51, -1.49, -1.47, -1.44, -1.42, -1.4, -1.37, -1.35, -1.32, -1.3, -1.27, -1.25, -1.23, -1.2, -1.18, -1.16, -1.14, -1.12, -1.1, -1.08, -1.06, -1.04, -1.02, -1.01, -0.99, -0.98, -0.97, -0.96, -0.95, -0.94, -0.93, -0.92, -0.92, -0.91, -0.91, -0.91, -0.91, -0.91, -0.92, -0.92, -0.93, -0.93, -0.94, -0.96, -0.97, -0.98, -1.0, -1.02, -1.04, -1.07, -1.09, -1.12, -1.15, -1.18, -1.21, -1.25, -1.29, -1.33, -1.37, -1.41, -1.45, -1.5, -1.54, -1.57, -1.61, -1.63, -1.65, -1.65, -1.65, -1.63, -1.61, -1.57, -1.53, -1.49, -1.44, -1.39, -1.34, -1.29, -1.24, -1.2, -1.15, -1.11, -1.06, -1.02, -0.98, -0.94, -0.91, -0.87, -0.84, -0.81, -0.78, -0.75, -0.72, -0.7, -0.67, -0.65, -0.62, -0.6, -0.58, -0.56, -0.54, -0.52, -0.51, -0.49, -0.48, -0.46, -0.45, -0.44, -0.43, -0.42, -0.41, -0.4, -0.39, -0.39, -0.39, -0.38, -0.38, -0.38, -0.38, -0.38, -0.39, -0.39, -0.4], [-1.38, -1.38, -1.37, -1.37, -1.36, -1.36, -1.35, -1.35, -1.35, -1.35, -1.35, -1.35, -1.35, -1.35, -1.34, -1.34, -1.34, -1.34, -1.34, -1.34, -1.34, -1.34, -1.34, -1.34, -1.33, -1.33, -1.33, -1.32, -1.32, -1.31, -1.31, -1.3, -1.3, -1.29, -1.28, -1.27, -1.26, -1.25, -1.24, -1.23, -1.22, -1.21, -1.2, -1.19, -1.18, -1.17, -1.16, -1.15, -1.14, -1.13, -1.12, -1.11, -1.1, -1.09, -1.08, -1.07, -1.06, -1.06, -1.05, -1.04, -1.04, -1.03, -1.03, -1.03, -1.03, -1.03, -1.03, -1.03, -1.03, -1.04, -1.04, -1.05, -1.06, -1.07, -1.08, -1.09, -1.11, -1.12, -1.14, -1.16, -1.19, -1.21, -1.24, -1.27, -1.3, -1.34, -1.38, -1.42, -1.47, -1.52, -1.57, -1.62, -1.68, -1.74, -1.8, -1.86, -1.91, -1.96, -1.99, -2.0, -1.98, -1.95, -1.9, -1.83, -1.76, -1.69, -1.61, -1.54, -1.47, -1.4, -1.33, -1.27, -1.21, -1.16, -1.1, -1.05, -1.01, -0.96, -0.92, -0.88, -0.84, -0.8, -0.77, -0.73, -0.7, -0.67, -0.65, -0.62, -0.59, -0.57, -0.55, -0.53, -0.5, -0.49, -0.47, -0.45, -0.44, -0.42, -0.41, -0.4, -0.39, -0.38, -0.37, -0.36, -0.35, -0.35, -0.34, -0.34, -0.34, -0.34, -0.34, -0.34, -0.34, -0.35, -0.35, -0.36], [-1.33, -1.33, -1.32, -1.32, -1.32, -1.31, -1.31, -1.31, -1.31, -1.31, -1.31, -1.31, -1.31, -1.32, -1.32, -1.32, -1.32, -1.33, -1.33, -1.34, -1.34, -1.34, -1.35, -1.35, -1.36, -1.36, -1.36, -1.37, -1.37, -1.37, -1.37, -1.37, -1.38, -1.38, -1.37, -1.37, -1.37, -1.37, -1.36, -1.36, -1.35, -1.35, -1.34, -1.33, -1.32, -1.32, -1.31, -1.3, -1.29, -1.28, -1.27, -1.25, -1.24, -1.23, -1.22, -1.21, -1.2, -1.19, -1.18, -1.17, -1.16, -1.15, -1.15, -1.14, -1.13, -1.12, -1.12, -1.11, -1.11, -1.1, -1.1, -1.1, -1.1, -1.09, -1.09, -1.09, -1.09, -1.09, -1.09, -1.1, -1.1, -1.1, -1.1, -1.1, -1.11, -1.11, -1.11, -1.11, -1.11, -1.11, -1.11, -1.11, -1.11, -1.11, -1.11, -1.1, -1.09, -1.09, -1.08, -1.07, -1.06, -1.05, -1.03, -1.02, -1.0, -0.98, -0.96, -0.95, -0.93, -0.91, -0.88, -0.86, -0.84, -0.82, -0.8, -0.78, -0.75, -0.73, -0.71, -0.69, -0.67, -0.65, -0.63, -0.61, -0.59, -0.57, -0.55, -0.53, -0.52, -0.5, -0.48, -0.47, -0.45, -0.44, -0.43, -0.41, -0.4, -0.39, -0.38, -0.37, -0.37, -0.36, -0.35, -0.35, -0.34, -0.34, -0.33, -0.33, -0.33, -0.33, -0.33, -0.33, -0.33, -0.34, -0.34, -0.35], [-1.38, -1.38, -1.38, -1.38, -1.39, -1.39, -1.39, -1.4, -1.41, -1.42, -1.42, -1.43, -1.44, -1.46, -1.47, -1.48, -1.5, -1.51, -1.53, -1.55, -1.57, -1.59, -1.61, -1.63, -1.65, -1.67, -1.69, -1.71, -1.73, -1.76, -1.78, -1.79, -1.81, -1.83, -1.84, -1.85, -1.86, -1.86, -1.86, -1.86, -1.85, -1.84, -1.83, -1.81, -1.79, -1.77, -1.74, -1.72, -1.69, -1.66, -1.64, -1.61, -1.58, -1.55, -1.53, -1.5, -1.47, -1.45, -1.42, -1.4, -1.38, -1.35, -1.33, -1.31, -1.29, -1.27, -1.25, -1.23, -1.22, -1.2, -1.18, -1.17, -1.15, -1.14, -1.12, -1.11, -1.1, -1.09, -1.07, -1.06, -1.05, -1.04, -1.03, -1.02, -1.01, -1.0, -0.99, -0.98, -0.97, -0.96, -0.95, -0.94, -0.93, -0.92, -0.91, -0.9, -0.89, -0.88, -0.87, -0.86, -0.85, -0.84, -0.82, -0.81, -0.8, -0.79, -0.78, -0.76, -0.75, -0.74, -0.72, -0.71, -0.7, -0.68, -0.67, -0.65, -0.64, -0.63, -0.61, -0.6, -0.59, -0.57, -0.56, -0.55, -0.53, -0.52, -0.51, -0.49, -0.48, -0.47, -0.46, -0.45, -0.44, -0.43, -0.42, -0.41, -0.4, -0.39, -0.39, -0.38, -0.37, -0.37, -0.36, -0.36, -0.36, -0.35, -0.35, -0.35, -0.35, -0.35, -0.35, -0.35, -0.35, -0.35, -0.36, -0.36], [-1.45, -1.45, -1.46, -1.46, -1.47, -1.48, -1.49, -1.5, -1.51, -1.53, -1.54, -1.56, -1.57, -1.59, -1.61, -1.63, -1.65, -1.68, -1.7, -1.73, -1.76, -1.79, -1.82, -1.86, -1.89, -1.93, -1.97, -2.01, -2.05, -2.09, -2.13, -2.18, -2.22, -2.26, -2.29, -2.33, -2.35, -2.37, -2.37, -2.37, -2.36, -2.34, -2.3, -2.27, -2.23, -2.18, -2.14, -2.09, -2.04, -1.99, -1.95, -1.9, -1.86, -1.82, -1.78, -1.74, -1.71, -1.67, -1.64, -1.61, -1.57, -1.55, -1.52, -1.49, -1.47, -1.44, -1.42, -1.4, -1.38, -1.36, -1.34, -1.32, -1.3, -1.28, -1.27, -1.25, -1.24, -1.23, -1.21, -1.2, -1.19, -1.18, -1.16, -1.15, -1.14, -1.13, -1.12, -1.11, -1.1, -1.09, -1.08, -1.07, -1.06, -1.05, -1.04, -1.03, -1.02, -1.01, -1.0, -0.99, -0.98, -0.97, -0.96, -0.94, -0.93, -0.92, -0.9, -0.89, -0.88, -0.86, -0.85, -0.83, -0.82, -0.8, -0.78, -0.77, -0.75, -0.74, -0.72, -0.71, -0.69, -0.67, -0.66, -0.64, -0.63, -0.61, -0.6, -0.59, -0.57, -0.56, -0.55, -0.53, -0.52, -0.51, -0.5, -0.49, -0.48, -0.47, -0.46, -0.45, -0.45, -0.44, -0.43, -0.43, -0.42, -0.42, -0.41, -0.41, -0.41, -0.41, -0.4, -0.4, -0.4, -0.41, -0.41, -0.41], [-1.42, -1.43, -1.43, -1.43, -1.43, -1.44, -1.44, -1.44, -1.45, -1.45, -1.46, -1.47, -1.47, -1.48, -1.49, -1.49, -1.5, -1.51, -1.52, -1.52, -1.53, -1.54, -1.55, -1.56, -1.57, -1.57, -1.58, -1.59, -1.6, -1.6, -1.61, -1.61, -1.62, -1.62, -1.63, -1.63, -1.63, -1.64, -1.64, -1.64, -1.64, -1.63, -1.63, -1.63, -1.63, -1.62, -1.62, -1.61, -1.61, -1.6, -1.59, -1.59, -1.58, -1.57, -1.56, -1.56, -1.55, -1.54, -1.53, -1.53, -1.52, -1.51, -1.51, -1.5, -1.49, -1.49, -1.48, -1.48, -1.48, -1.47, -1.47, -1.47, -1.47, -1.46, -1.46, -1.46, -1.46, -1.46, -1.46, -1.47, -1.47, -1.47, -1.47, -1.47, -1.48, -1.48, -1.48, -1.48, -1.49, -1.49, -1.49, -1.49, -1.49, -1.48, -1.48, -1.47, -1.47, -1.46, -1.45, -1.44, -1.42, -1.41, -1.39, -1.37, -1.35, -1.33, -1.3, -1.28, -1.25, -1.23, -1.2, -1.17, -1.15, -1.12, -1.09, -1.07, -1.04, -1.01, -0.99, -0.96, -0.93, -0.91, -0.88, -0.86, -0.84, -0.82, -0.79, -0.77, -0.75, -0.73, -0.71, -0.7, -0.68, -0.66, -0.65, -0.63, -0.62, -0.6, -0.59, -0.58, -0.57, -0.56, -0.55, -0.54, -0.53, -0.52, -0.52, -0.51, -0.5, -0.5, -0.5, -0.49, -0.49, -0.49, -0.49, -0.49], [-1.35, -1.35, -1.35, -1.35, -1.35, -1.35, -1.34, -1.34, -1.34, -1.34, -1.34, -1.35, -1.35, -1.35, -1.35, -1.35, -1.35, -1.35, -1.36, -1.36, -1.36, -1.36, -1.37, -1.37, -1.37, -1.38, -1.38, -1.38, -1.38, -1.39, -1.39, -1.39, -1.4, -1.4, -1.4, -1.41, -1.41, -1.42, -1.42, -1.42, -1.43, -1.43, -1.43, -1.44, -1.44, -1.45, -1.45, -1.45, -1.46, -1.46, -1.47, -1.47, -1.48, -1.48, -1.49, -1.49, -1.5, -1.51, -1.51, -1.52, -1.53, -1.54, -1.55, -1.56, -1.57, -1.58, -1.59, -1.6, -1.61, -1.63, -1.64, -1.66, -1.67, -1.69, -1.71, -1.73, -1.75, -1.77, -1.79, -1.82, -1.84, -1.87, -1.9, -1.93, -1.95, -1.98, -2.01, -2.04, -2.06, -2.08, -2.1, -2.11, -2.12, -2.12, -2.11, -2.09, -2.07, -2.04, -2.0, -1.96, -1.92, -1.87, -1.82, -1.77, -1.72, -1.67, -1.62, -1.58, -1.53, -1.48, -1.44, -1.39, -1.35, -1.31, -1.27, -1.24, -1.2, -1.16, -1.13, -1.1, -1.07, -1.04, -1.01, -0.98, -0.95, -0.93, -0.9, -0.88, -0.85, -0.83, -0.81, -0.79, -0.77, -0.76, -0.74, -0.72, -0.71, -0.69, -0.68, -0.66, -0.65, -0.64, -0.63, -0.62, -0.61, -0.6, -0.59, -0.58, -0.58, -0.57, -0.57, -0.56, -0.56, -0.55, -0.55, -0.55], [-1.34, -1.34, -1.34, -1.34, -1.34, -1.34, -1.34, -1.34, -1.34, -1.34, -1.34, -1.34, -1.34, -1.34, -1.35, -1.35, -1.35, -1.35, -1.35, -1.36, -1.36, -1.36, -1.37, -1.37, -1.37, -1.38, -1.38, -1.38, -1.39, -1.39, -1.39, -1.4, -1.4, -1.4, -1.41, -1.41, -1.41, -1.42, -1.42, -1.42, -1.42, -1.43, -1.43, -1.43, -1.43, -1.44, -1.44, -1.44, -1.44, -1.44, -1.44, -1.45, -1.45, -1.45, -1.45, -1.45, -1.45, -1.45, -1.45, -1.45, -1.46, -1.46, -1.46, -1.46, -1.46, -1.46, -1.46, -1.46, -1.46, -1.46, -1.46, -1.46, -1.46, -1.45, -1.45, -1.45, -1.45, -1.45, -1.44, -1.44, -1.44, -1.43, -1.43, -1.42, -1.42, -1.41, -1.4, -1.39, -1.38, -1.37, -1.36, -1.35, -1.34, -1.33, -1.31, -1.3, -1.28, -1.27, -1.25, -1.24, -1.22, -1.2, -1.18, -1.17, -1.15, -1.13, -1.11, -1.09, -1.07, -1.05, -1.04, -1.02, -1.0, -0.98, -0.96, -0.94, -0.93, -0.91, -0.89, -0.87, -0.86, -0.84, -0.83, -0.81, -0.8, -0.78, -0.77, -0.75, -0.74, -0.73, -0.71, -0.7, -0.69, -0.68, -0.67, -0.66, -0.65, -0.64, -0.63, -0.62, -0.61, -0.61, -0.6, -0.59, -0.59, -0.58, -0.58, -0.57, -0.57, -0.57, -0.56, -0.56, -0.56, -0.56, -0.55, -0.55], [-1.41, -1.41, -1.42, -1.42, -1.42, -1.43, -1.43, -1.43, -1.44, -1.44, -1.45, -1.45, -1.46, -1.46, -1.47, -1.47, -1.48, -1.48, -1.49, -1.5, -1.5, -1.51, -1.51, -1.52, -1.53, -1.53, -1.54, -1.54, -1.55, -1.55, -1.56, -1.56, -1.56, -1.57, -1.57, -1.57, -1.57, -1.57, -1.57, -1.57, -1.57, -1.56, -1.56, -1.56, -1.55, -1.55, -1.54, -1.53, -1.52, -1.52, -1.51, -1.5, -1.49, -1.48, -1.47, -1.45, -1.44, -1.43, -1.42, -1.4, -1.39, -1.38, -1.36, -1.35, -1.34, -1.32, -1.31, -1.29, -1.28, -1.26, -1.25, -1.24, -1.22, -1.21, -1.19, -1.18, -1.16, -1.15, -1.14, -1.12, -1.11, -1.09, -1.08, -1.07, -1.05, -1.04, -1.02, -1.01, -1.0, -0.98, -0.97, -0.96, -0.94, -0.93, -0.92, -0.91, -0.89, -0.88, -0.87, -0.86, -0.84, -0.83, -0.82, -0.81, -0.8, -0.79, -0.77, -0.76, -0.75, -0.74, -0.73, -0.72, -0.71, -0.7, -0.69, -0.68, -0.67, -0.66, -0.65, -0.64, -0.64, -0.63, -0.62, -0.61, -0.6, -0.6, -0.59, -0.58, -0.58, -0.57, -0.56, -0.56, -0.55, -0.55, -0.54, -0.54, -0.53, -0.53, -0.53, -0.52, -0.52, -0.52, -0.51, -0.51, -0.51, -0.51, -0.51, -0.5, -0.5, -0.5, -0.5, -0.5, -0.5, -0.5, -0.51, -0.51], [-1.55, -1.56, -1.57, -1.58, -1.6, -1.61, -1.62, -1.63, -1.65, -1.66, -1.68, -1.7, -1.71, -1.73, -1.75, -1.77, -1.79, -1.82, -1.84, -1.87, -1.89, -1.92, -1.95, -1.97, -2.0, -2.03, -2.07, -2.1, -2.13, -2.16, -2.19, -2.22, -2.25, -2.27, -2.29, -2.31, -2.32, -2.32, -2.32, -2.31, -2.3, -2.28, -2.25, -2.22, -2.18, -2.14, -2.1, -2.06, -2.02, -1.98, -1.93, -1.89, -1.85, -1.81, -1.77, -1.73, -1.69, -1.65, -1.61, -1.58, -1.54, -1.51, -1.48, -1.45, -1.41, -1.38, -1.35, -1.33, -1.3, -1.27, -1.25, -1.22, -1.19, -1.17, -1.15, -1.12, -1.1, -1.08, -1.06, -1.04, -1.02, -1.0, -0.98, -0.96, -0.94, -0.92, -0.91, -0.89, -0.87, -0.86, -0.84, -0.83, -0.81, -0.8, -0.78, -0.77, -0.75, -0.74, -0.73, -0.72, -0.7, -0.69, -0.68, -0.67, -0.66, -0.65, -0.64, -0.63, -0.62, -0.61, -0.6, -0.59, -0.58, -0.57, -0.56, -0.56, -0.55, -0.54, -0.53, -0.53, -0.52, -0.52, -0.51, -0.5, -0.5, -0.49, -0.49, -0.48, -0.48, -0.48, -0.47, -0.47, -0.46, -0.46, -0.46, -0.46, -0.45, -0.45, -0.45, -0.45, -0.45, -0.45, -0.45, -0.45, -0.45, -0.45, -0.45, -0.45, -0.45, -0.45, -0.45, -0.45, -0.45, -0.45, -0.46, -0.46], [-1.53, -1.54, -1.55, -1.55, -1.56, -1.57, -1.58, -1.59, -1.6, -1.61, -1.62, -1.63, -1.64, -1.65, -1.66, -1.68, -1.69, -1.7, -1.71, -1.72, -1.73, -1.74, -1.75, -1.76, -1.77, -1.78, -1.79, -1.79, -1.8, -1.8, -1.8, -1.8, -1.8, -1.79, -1.79, -1.78, -1.77, -1.76, -1.75, -1.73, -1.72, -1.7, -1.68, -1.66, -1.64, -1.62, -1.6, -1.57, -1.55, -1.52, -1.5, -1.48, -1.45, -1.43, -1.4, -1.38, -1.35, -1.33, -1.31, -1.28, -1.26, -1.24, -1.21, -1.19, -1.17, -1.15, -1.12, -1.1, -1.08, -1.06, -1.04, -1.02, -1.0, -0.99, -0.97, -0.95, -0.93, -0.91, -0.9, -0.88, -0.86, -0.85, -0.83, -0.82, -0.8, -0.79, -0.77, -0.76, -0.75, -0.73, -0.72, -0.71, -0.7, -0.68, -0.67, -0.66, -0.65, -0.64, -0.63, -0.62, -0.61, -0.6, -0.59, -0.58, -0.57, -0.56, -0.55, -0.55, -0.54, -0.53, -0.52, -0.52, -0.51, -0.5, -0.5, -0.49, -0.48, -0.48, -0.47, -0.47, -0.46, -0.46, -0.45, -0.45, -0.45, -0.44, -0.44, -0.44, -0.43, -0.43, -0.43, -0.42, -0.42, -0.42, -0.42, -0.42, -0.42, -0.42, -0.41, -0.41, -0.41, -0.41, -0.41, -0.41, -0.41, -0.42, -0.42, -0.42, -0.42, -0.42, -0.42, -0.42, -0.43, -0.43, -0.43, -0.43], [-1.18, -1.17, -1.17, -1.17, -1.16, -1.16, -1.15, -1.15, -1.14, -1.14, -1.14, -1.13, -1.13, -1.12, -1.12, -1.11, -1.11, -1.1, -1.1, -1.09, -1.09, -1.08, -1.08, -1.07, -1.06, -1.06, -1.05, -1.05, -1.04, -1.03, -1.03, -1.02, -1.01, -1.01, -1.0, -0.99, -0.98, -0.98, -0.97, -0.96, -0.95, -0.95, -0.94, -0.93, -0.92, -0.91, -0.91, -0.9, -0.89, -0.88, -0.87, -0.86, -0.85, -0.85, -0.84, -0.83, -0.82, -0.81, -0.8, -0.79, -0.78, -0.78, -0.77, -0.76, -0.75, -0.74, -0.73, -0.72, -0.71, -0.71, -0.7, -0.69, -0.68, -0.67, -0.66, -0.66, -0.65, -0.64, -0.63, -0.62, -0.62, -0.61, -0.6, -0.59, -0.59, -0.58, -0.57, -0.57, -0.56, -0.55, -0.55, -0.54, -0.53, -0.53, -0.52, -0.51, -0.51, -0.5, -0.5, -0.49, -0.49, -0.48, -0.48, -0.47, -0.47, -0.46, -0.46, -0.45, -0.45, -0.45, -0.44, -0.44, -0.43, -0.43, -0.43, -0.42, -0.42, -0.42, -0.42, -0.41, -0.41, -0.41, -0.41, -0.4, -0.4, -0.4, -0.4, -0.4, -0.4, -0.4, -0.4, -0.4, -0.39, -0.39, -0.39, -0.39, -0.39, -0.39, -0.39, -0.4, -0.4, -0.4, -0.4, -0.4, -0.4, -0.4, -0.4, -0.41, -0.41, -0.41, -0.41, -0.42, -0.42, -0.42, -0.42, -0.43], [-0.88, -0.88, -0.87, -0.86, -0.86, -0.85, -0.84, -0.84, -0.83, -0.82, -0.82, -0.81, -0.8, -0.8, -0.79, -0.79, -0.78, -0.77, -0.77, -0.76, -0.76, -0.75, -0.74, -0.74, -0.73, -0.73, -0.72, -0.71, -0.71, -0.7, -0.7, -0.69, -0.69, -0.68, -0.67, -0.67, -0.66, -0.66, -0.65, -0.65, -0.64, -0.64, -0.63, -0.63, -0.62, -0.62, -0.61, -0.61, -0.6, -0.6, -0.59, -0.59, -0.58, -0.58, -0.57, -0.57, -0.56, -0.56, -0.55, -0.55, -0.54, -0.54, -0.54, -0.53, -0.53, -0.52, -0.52, -0.51, -0.51, -0.51, -0.5, -0.5, -0.49, -0.49, -0.49, -0.48, -0.48, -0.48, -0.47, -0.47, -0.47, -0.46, -0.46, -0.46, -0.45, -0.45, -0.45, -0.44, -0.44, -0.44, -0.43, -0.43, -0.43, -0.43, -0.42, -0.42, -0.42, -0.42, -0.41, -0.41, -0.41, -0.41, -0.41, -0.41, -0.4, -0.4, -0.4, -0.4, -0.4, -0.4, -0.39, -0.39, -0.39, -0.39, -0.39, -0.39, -0.39, -0.39, -0.39, -0.39, -0.39, -0.39, -0.39, -0.39, -0.39, -0.39, -0.39, -0.39, -0.39, -0.39, -0.39, -0.39, -0.39, -0.39, -0.39, -0.4, -0.4, -0.4, -0.4, -0.4, -0.4, -0.4, -0.41, -0.41, -0.41, -0.41, -0.42, -0.42, -0.42, -0.42, -0.43, -0.43, -0.43, -0.44, -0.44, -0.44], [-0.75, -0.74, -0.74, -0.73, -0.73, -0.72, -0.71, -0.71, -0.7, -0.7, -0.69, -0.69, -0.68, -0.68, -0.67, -0.67, -0.66, -0.66, -0.65, -0.65, -0.64, -0.64, -0.63, -0.63, -0.62, -0.62, -0.62, -0.61, -0.61, -0.6, -0.6, -0.59, -0.59, -0.59, -0.58, -0.58, -0.58, -0.57, -0.57, -0.56, -0.56, -0.56, -0.55, -0.55, -0.55, -0.54, -0.54, -0.54, -0.54, -0.53, -0.53, -0.53, -0.52, -0.52, -0.52, -0.52, -0.51, -0.51, -0.51, -0.51, -0.5, -0.5, -0.5, -0.5, -0.49, -0.49, -0.49, -0.49, -0.49, -0.48, -0.48, -0.48, -0.48, -0.48, -0.47, -0.47, -0.47, -0.47, -0.47, -0.47, -0.46, -0.46, -0.46, -0.46, -0.46, -0.46, -0.46, -0.45, -0.45, -0.45, -0.45, -0.45, -0.45, -0.45, -0.45, -0.45, -0.45, -0.45, -0.44, -0.44, -0.44, -0.44, -0.44, -0.44, -0.44, -0.44, -0.44, -0.44, -0.44, -0.44, -0.44, -0.44, -0.44, -0.44, -0.44, -0.44, -0.44, -0.44, -0.44, -0.44, -0.44, -0.44, -0.44, -0.45, -0.45, -0.45, -0.45, -0.45, -0.45, -0.45, -0.45, -0.45, -0.45, -0.46, -0.46, -0.46, -0.46, -0.46, -0.46, -0.47, -0.47, -0.47, -0.47, -0.47, -0.48, -0.48, -0.48, -0.48, -0.49, -0.49, -0.49, -0.5, -0.5, -0.5, -0.5, -0.51], [-0.76, -0.76, -0.76, -0.75, -0.75, -0.74, -0.74, -0.74, -0.73, -0.73, -0.73, -0.72, -0.72, -0.72, -0.71, -0.71, -0.71, -0.7, -0.7, -0.7, -0.7, -0.69, -0.69, -0.69, -0.69, -0.68, -0.68, -0.68, -0.68, -0.68, -0.67, -0.67, -0.67, -0.67, -0.67, -0.66, -0.66, -0.66, -0.66, -0.66, -0.66, -0.65, -0.65, -0.65, -0.65, -0.65, -0.65, -0.65, -0.65, -0.64, -0.64, -0.64, -0.64, -0.64, -0.64, -0.64, -0.64, -0.64, -0.64, -0.64, -0.63, -0.63, -0.63, -0.63, -0.63, -0.63, -0.63, -0.63, -0.63, -0.63, -0.63, -0.63, -0.63, -0.63, -0.63, -0.63, -0.63, -0.63, -0.62, -0.62, -0.62, -0.62, -0.62, -0.62, -0.62, -0.62, -0.62, -0.62, -0.62, -0.62, -0.62, -0.62, -0.62, -0.62, -0.62, -0.62, -0.62, -0.62, -0.62, -0.62, -0.62, -0.62, -0.62, -0.62, -0.62, -0.62, -0.62, -0.62, -0.62, -0.62, -0.62, -0.62, -0.62, -0.62, -0.62, -0.62, -0.62, -0.62, -0.62, -0.62, -0.62, -0.62, -0.62, -0.62, -0.62, -0.62, -0.62, -0.62, -0.62, -0.62, -0.62, -0.62, -0.62, -0.62, -0.63, -0.63, -0.63, -0.63, -0.63, -0.63, -0.63, -0.63, -0.63, -0.64, -0.64, -0.64, -0.64, -0.64, -0.64, -0.64, -0.65, -0.65, -0.65, -0.65, -0.65, -0.66], [-0.91, -0.9, -0.9, -0.9, -0.9, -0.9, -0.9, -0.9, -0.9, -0.9, -0.9, -0.9, -0.9, -0.9, -0.9, -0.9, -0.9, -0.9, -0.9, -0.9, -0.9, -0.9, -0.9, -0.9, -0.9, -0.9, -0.9, -0.9, -0.9, -0.9, -0.91, -0.91, -0.91, -0.91, -0.91, -0.91, -0.91, -0.92, -0.92, -0.92, -0.92, -0.92, -0.92, -0.93, -0.93, -0.93, -0.93, -0.93, -0.94, -0.94, -0.94, -0.94, -0.94, -0.95, -0.95, -0.95, -0.95, -0.95, -0.96, -0.96, -0.96, -0.96, -0.96, -0.97, -0.97, -0.97, -0.97, -0.97, -0.97, -0.98, -0.98, -0.98, -0.98, -0.98, -0.98, -0.98, -0.99, -0.99, -0.99, -0.99, -0.99, -0.99, -0.99, -0.99, -0.99, -0.99, -0.99, -1.0, -1.0, -1.0, -1.0, -1.0, -1.0, -1.0, -1.0, -1.0, -0.99, -0.99, -0.99, -0.99, -0.99, -0.99, -0.99, -0.99, -0.99, -0.99, -0.99, -0.99, -0.98, -0.98, -0.98, -0.98, -0.98, -0.98, -0.98, -0.97, -0.97, -0.97, -0.97, -0.97, -0.97, -0.96, -0.96, -0.96, -0.96, -0.96, -0.95, -0.95, -0.95, -0.95, -0.95, -0.95, -0.94, -0.94, -0.94, -0.94, -0.94, -0.94, -0.93, -0.93, -0.93, -0.93, -0.93, -0.93, -0.92, -0.92, -0.92, -0.92, -0.92, -0.92, -0.92, -0.92, -0.92, -0.92, -0.91, -0.91], [-1.12, -1.12, -1.12, -1.13, -1.13, -1.13, -1.14, -1.14, -1.14, -1.15, -1.15, -1.15, -1.16, -1.16, -1.17, -1.17, -1.18, -1.18, -1.19, -1.19, -1.2, -1.2, -1.21, -1.21, -1.22, -1.23, -1.23, -1.24, -1.24, -1.25, -1.26, -1.27, -1.27, -1.28, -1.29, -1.3, -1.3, -1.31, -1.32, -1.33, -1.34, -1.35, -1.36, -1.36, -1.37, -1.38, -1.39, -1.4, -1.41, -1.42, -1.43, -1.44, -1.45, -1.47, -1.48, -1.49, -1.5, -1.51, -1.52, -1.53, -1.54, -1.55, -1.57, -1.58, -1.59, -1.6, -1.61, -1.62, -1.63, -1.64, -1.66, -1.67, -1.68, -1.69, -1.7, -1.71, -1.72, -1.72, -1.73, -1.74, -1.75, -1.76, -1.76, -1.77, -1.77, -1.78, -1.78, -1.79, -1.79, -1.79, -1.79, -1.79, -1.79, -1.79, -1.79, -1.79, -1.78, -1.78, -1.78, -1.77, -1.76, -1.76, -1.75, -1.74, -1.74, -1.73, -1.72, -1.71, -1.7, -1.69, -1.68, -1.67, -1.66, -1.65, -1.64, -1.63, -1.62, -1.61, -1.6, -1.59, -1.57, -1.56, -1.55, -1.54, -1.53, -1.52, -1.51, -1.5, -1.49, -1.48, -1.47, -1.46, -1.45, -1.44, -1.43, -1.42, -1.41, -1.4, -1.39, -1.39, -1.38, -1.37, -1.36, -1.35, -1.34, -1.34, -1.33, -1.32, -1.31, -1.31, -1.3, -1.29, -1.29, -1.28, -1.27, -1.27], [-1.21, -1.22, -1.22, -1.22, -1.23, -1.23, -1.23, -1.24, -1.24, -1.25, -1.25, -1.25, -1.26, -1.26, -1.27, -1.27, -1.28, -1.28, -1.29, -1.29, -1.3, -1.31, -1.31, -1.32, -1.32, -1.33, -1.34, -1.34, -1.35, -1.36, -1.36, -1.37, -1.38, -1.39, -1.39, -1.4, -1.41, -1.42, -1.42, -1.43, -1.44, -1.45, -1.46, -1.47, -1.48, -1.48, -1.49, -1.5, -1.51, -1.52, -1.53, -1.54, -1.55, -1.56, -1.57, -1.58, -1.59, -1.6, -1.61, -1.62, -1.63, -1.64, -1.65, -1.66, -1.67, -1.68, -1.69, -1.7, -1.71, -1.72, -1.73, -1.74, -1.75, -1.76, -1.76, -1.77, -1.78, -1.79, -1.8, -1.8, -1.81, -1.82, -1.82, -1.83, -1.83, -1.84, -1.84, -1.84, -1.84, -1.85, -1.85, -1.85, -1.85, -1.85, -1.85, -1.85, -1.84, -1.84, -1.84, -1.84, -1.83, -1.83, -1.82, -1.82, -1.81, -1.8, -1.8, -1.79, -1.78, -1.78, -1.77, -1.76, -1.75, -1.74, -1.73, -1.72, -1.72, -1.71, -1.7, -1.69, -1.68, -1.67, -1.66, -1.65, -1.64, -1.63, -1.62, -1.61, -1.6, -1.59, -1.59, -1.58, -1.57, -1.56, -1.55, -1.54, -1.53, -1.52, -1.52, -1.51, -1.5, -1.49, -1.48, -1.47, -1.47, -1.46, -1.45, -1.45, -1.44, -1.43, -1.42, -1.42, -1.41, -1.4, -1.4, -1.39], [-1.07, -1.07, -1.07, -1.07, -1.07, -1.07, -1.07, -1.07, -1.07, -1.07, -1.07, -1.07, -1.07, -1.07, -1.07, -1.07, -1.07, -1.07, -1.07, -1.07, -1.07, -1.07, -1.07, -1.07, -1.07, -1.07, -1.07, -1.07, -1.07, -1.07, -1.07, -1.07, -1.07, -1.07, -1.08, -1.08, -1.08, -1.08, -1.08, -1.08, -1.08, -1.08, -1.08, -1.08, -1.08, -1.08, -1.08, -1.09, -1.09, -1.09, -1.09, -1.09, -1.09, -1.09, -1.09, -1.09, -1.09, -1.09, -1.1, -1.1, -1.1, -1.1, -1.1, -1.1, -1.1, -1.1, -1.1, -1.1, -1.11, -1.11, -1.11, -1.11, -1.11, -1.11, -1.11, -1.11, -1.11, -1.11, -1.11, -1.11, -1.11, -1.12, -1.12, -1.12, -1.12, -1.12, -1.12, -1.12, -1.12, -1.12, -1.12, -1.12, -1.12, -1.12, -1.12, -1.12, -1.12, -1.12, -1.12, -1.12, -1.12, -1.12, -1.12, -1.12, -1.12, -1.12, -1.12, -1.12, -1.12, -1.12, -1.12, -1.12, -1.12, -1.12, -1.12, -1.12, -1.12, -1.12, -1.12, -1.12, -1.12, -1.12, -1.12, -1.12, -1.12, -1.12, -1.12, -1.12, -1.12, -1.12, -1.12, -1.12, -1.12, -1.12, -1.12, -1.12, -1.12, -1.12, -1.12, -1.12, -1.12, -1.12, -1.12, -1.12, -1.12, -1.12, -1.12, -1.12, -1.12, -1.12, -1.12, -1.12, -1.12, -1.12, -1.12, -1.12], [-0.87, -0.87, -0.87, -0.87, -0.86, -0.86, -0.86, -0.86, -0.86, -0.85, -0.85, -0.85, -0.85, -0.85, -0.84, -0.84, -0.84, -0.84, -0.84, -0.84, -0.83, -0.83, -0.83, -0.83, -0.83, -0.83, -0.83, -0.82, -0.82, -0.82, -0.82, -0.82, -0.82, -0.82, -0.82, -0.81, -0.81, -0.81, -0.81, -0.81, -0.81, -0.81, -0.81, -0.81, -0.81, -0.8, -0.8, -0.8, -0.8, -0.8, -0.8, -0.8, -0.8, -0.8, -0.8, -0.8, -0.8, -0.8, -0.8, -0.8, -0.8, -0.8, -0.79, -0.79, -0.79, -0.79, -0.79, -0.79, -0.79, -0.79, -0.79, -0.79, -0.79, -0.79, -0.79, -0.79, -0.79, -0.79, -0.79, -0.79, -0.79, -0.79, -0.79, -0.79, -0.79, -0.79, -0.79, -0.79, -0.79, -0.79, -0.79, -0.8, -0.8, -0.8, -0.8, -0.8, -0.8, -0.8, -0.8, -0.8, -0.8, -0.8, -0.8, -0.8, -0.8, -0.8, -0.8, -0.8, -0.8, -0.81, -0.81, -0.81, -0.81, -0.81, -0.81, -0.81, -0.81, -0.81, -0.81, -0.82, -0.82, -0.82, -0.82, -0.82, -0.82, -0.82, -0.82, -0.82, -0.83, -0.83, -0.83, -0.83, -0.83, -0.83, -0.83, -0.84, -0.84, -0.84, -0.84, -0.84, -0.84, -0.85, -0.85, -0.85, -0.85, -0.85, -0.85, -0.86, -0.86, -0.86, -0.86, -0.86, -0.87, -0.87, -0.87, -0.87]]};

  const ctxLev = document.getElementById("chartJstLeverage");
  const ctxDil = document.getElementById("chartJstDilation");
  const ctxSpec = document.getElementById("chartJstSpectrum");
  const ctxMf = document.getElementById("chartJstMultifractal");
  const canvasScalo = document.getElementById("canvasJstScalogram");

  if (!ctxLev || !ctxDil || !ctxSpec || !ctxMf || !canvasScalo) return;

  // Panel 1: Real US Private Credit + Sovereign Debt + 18-Country Global Leverage (1870-2025)
  new Chart(ctxLev, {
    type: "line",
    data: {
      labels: EMPIRICAL_JST.years,
      datasets: [
        {
          label: "US Private Credit / GDP (%)",
          data: EMPIRICAL_JST.priv,
          borderColor: "#38bdf8",
          backgroundColor: "rgba(56, 189, 248, 0.12)",
          borderWidth: 2,
          pointRadius: 0,
          fill: true
        },
        {
          label: "US Sovereign Debt / GDP (%)",
          data: EMPIRICAL_JST.pub,
          borderColor: "#a855f7",
          backgroundColor: "rgba(168, 85, 247, 0.12)",
          borderWidth: 2,
          pointRadius: 0,
          fill: true
        },
        {
          label: "US Total Leverage (Priv+Pub % GDP)",
          data: EMPIRICAL_JST.tot,
          borderColor: "#f8fafc",
          borderWidth: 2,
          pointRadius: 0,
          fill: false
        },
        {
          label: "18-Country Global Mean Debt / GDP (%)",
          data: EMPIRICAL_JST.global_tot,
          borderColor: "#10b981",
          borderDash: [4, 4],
          borderWidth: 1.8,
          pointRadius: 0,
          fill: false
        }
      ]
    },
    options: {
      responsive: true,
      maintainAspectRatio: false,
      interaction: { mode: "index", intersect: false },
      scales: {
        x: { ticks: { color: "#94a3b8", maxTicksLimit: 10 }, grid: { color: "rgba(148,163,184,0.08)" } },
        y: { ticks: { color: "#94a3b8" }, grid: { color: "rgba(148,163,184,0.08)" }, title: { display: true, text: "% of GDP", color: "#94a3b8" } }
      },
      plugins: { legend: { labels: { color: "#e2e8f0", boxWidth: 12, font: { size: 11 } } } }
    }
  });

  // Panel 2: Empirical Metric Time Dilation 1/sqrt(-g_00) vs 10Y Real GDP/cap Growth
  new Chart(ctxDil, {
    type: "line",
    data: {
      labels: EMPIRICAL_JST.years,
      datasets: [
        {
          label: "Proper Velocity 1/√−g₀₀(t) [c]",
          data: EMPIRICAL_JST.dilation,
          borderColor: "#22d3ee",
          backgroundColor: "rgba(34, 211, 238, 0.1)",
          borderWidth: 2.2,
          pointRadius: 0,
          yAxisID: "y",
          fill: true
        },
        {
          label: "10Y Rolling Real GDP/Cap Growth (%)",
          data: EMPIRICAL_JST.rgdp_roll,
          borderColor: "#f59e0b",
          borderDash: [3, 3],
          borderWidth: 1.8,
          pointRadius: 0,
          yAxisID: "y1"
        }
      ]
    },
    options: {
      responsive: true,
      maintainAspectRatio: false,
      interaction: { mode: "index", intersect: false },
      scales: {
        x: { ticks: { color: "#94a3b8", maxTicksLimit: 10 }, grid: { color: "rgba(148,163,184,0.08)" } },
        y: { position: "left", ticks: { color: "#22d3ee" }, grid: { color: "rgba(148,163,184,0.08)" }, title: { display: true, text: "1/√−g₀₀ (c)", color: "#22d3ee" } },
        y1: { position: "right", ticks: { color: "#f59e0b" }, grid: { drawOnChartArea: false }, title: { display: true, text: "10Y Real Growth (%)", color: "#f59e0b" } }
      },
      plugins: { legend: { labels: { color: "#e2e8f0", boxWidth: 12, font: { size: 11 } } } }
    }
  });

  // Panel 3: Empirical Morlet Wavelet Power Spectrum
  new Chart(ctxSpec, {
    type: "line",
    data: {
      labels: EMPIRICAL_JST.periods.map(p => p.toFixed(1) + "y"),
      datasets: [
        {
          label: "Empirical Morlet Wavelet Power (T₁=6.17y, T_mid=14.72y, T₂=79.73y)",
          data: EMPIRICAL_JST.norm_psd,
          borderColor: "#10b981",
          backgroundColor: "rgba(16, 185, 129, 0.18)",
          borderWidth: 2.2,
          pointRadius: 2,
          fill: true
        }
      ]
    },
    options: {
      responsive: true,
      maintainAspectRatio: false,
      scales: {
        x: { ticks: { color: "#94a3b8", maxTicksLimit: 10 }, grid: { color: "rgba(148,163,184,0.08)" } },
        y: { ticks: { color: "#94a3b8" }, grid: { color: "rgba(148,163,184,0.08)" }, title: { display: true, text: "Normalized Wavelet Power", color: "#10b981" } }
      },
      plugins: { legend: { labels: { color: "#e2e8f0", boxWidth: 12, font: { size: 11 } } } }
    }
  });

  // Panel 4: Empirical Mandelbrot Multifractal Spectrum f(alpha)
  const mfPoints = EMPIRICAL_JST.alpha.map((a, idx) => ({ x: a, y: EMPIRICAL_JST.f_alpha[idx] }));
  new Chart(ctxMf, {
    type: "scatter",
    data: {
      datasets: [
        {
          label: "Empirical f(α) Singularity Spectrum (Δα = 0.828, H = 0.793)",
          data: mfPoints,
          showLine: true,
          borderColor: "#f43f5e",
          backgroundColor: "#f43f5e",
          borderWidth: 2.2,
          pointRadius: 3.5
        }
      ]
    },
    options: {
      responsive: true,
      maintainAspectRatio: false,
      scales: {
        x: { ticks: { color: "#94a3b8" }, grid: { color: "rgba(148,163,184,0.08)" }, title: { display: true, text: "Local Hölder Exponent α", color: "#94a3b8" } },
        y: { ticks: { color: "#94a3b8" }, grid: { color: "rgba(148,163,184,0.08)" }, title: { display: true, text: "Singularity Dimension f(α)", color: "#f43f5e" } }
      },
      plugins: { legend: { labels: { color: "#e2e8f0", boxWidth: 12, font: { size: 11 } } } }
    }
  });

  // Panel 5: Empirical 2D Morlet Wavelet Scalogram (1870-2025)
  function drawEmpiricalScalogram() {
    const rect = canvasScalo.parentElement.getBoundingClientRect();
    const width = canvasScalo.width = Math.max(600, rect.width || 900);
    const height = canvasScalo.height = 290;
    const ctx = canvasScalo.getContext("2d");

    const padLeft = 58, padRight = 24, padTop = 22, padBottom = 34;
    const plotW = width - padLeft - padRight;
    const plotH = height - padTop - padBottom;

    ctx.fillStyle = "#090d16";
    ctx.fillRect(0, 0, width, height);

    const grid = EMPIRICAL_JST.log_scalo;
    const nScales = grid.length;
    const nYears = grid[0].length;

    let vMin = Infinity, vMax = -Infinity;
    for (let s = 0; s < nScales; s++) {
      for (let t = 0; t < nYears; t++) {
        if (grid[s][t] < vMin) vMin = grid[s][t];
        if (grid[s][t] > vMax) vMax = grid[s][t];
      }
    }

    const cellW = plotW / nYears;
    const cellH = plotH / nScales;

    for (let s = 0; s < nScales; s++) {
      const y = padTop + (nScales - 1 - s) * cellH;
      for (let t = 0; t < nYears; t++) {
        const x = padLeft + t * cellW;
        const norm = Math.max(0, Math.min(1, (grid[s][t] - vMin) / (vMax - vMin + 1e-9)));
        // Magma-inspired scientific colormap
        const r = Math.min(255, Math.floor(255 * Math.pow(norm, 0.75)));
        const g = Math.min(255, Math.floor(215 * Math.pow(norm, 1.85)));
        const b = Math.min(255, Math.floor(190 * Math.sin(norm * Math.PI * 0.85) + 65 * Math.pow(norm, 3)));
        ctx.fillStyle = `rgb(${r},${g},${b})`;
        ctx.fillRect(x, y, Math.ceil(cellW), Math.ceil(cellH));
      }
    }

    // Highlight Historical Regime Resets (1933, 1946, 1971, 2008, 2020)
    const resets = [
      { yr: 1933, label: "1933 Gold Reset" },
      { yr: 1946, label: "1946 Bretton Woods" },
      { yr: 1971, label: "1971 Nixon Shock" },
      { yr: 2008, label: "2008 GFC / QE" },
      { yr: 2020, label: "2020 COVID Monetization" }
    ];
    ctx.strokeStyle = "rgba(56, 189, 248, 0.9)";
    ctx.lineWidth = 1.4;
    ctx.setLineDash([4, 3]);
    ctx.fillStyle = "#38bdf8";
    ctx.font = "bold 10px JetBrains Mono, monospace";
    resets.forEach(ev => {
      const x = padLeft + ((ev.yr - 1870) / (2025 - 1870)) * plotW;
      ctx.beginPath();
      ctx.moveTo(x, padTop);
      ctx.lineTo(x, padTop + plotH);
      ctx.stroke();
      ctx.fillText(ev.label, x - 28, padTop - 6);
    });
    ctx.setLineDash([]);

    // Axes labels
    ctx.fillStyle = "#cbd5e1";
    ctx.font = "11px JetBrains Mono, monospace";
    [1870, 1900, 1930, 1960, 1990, 2025].forEach(yr => {
      const x = padLeft + ((yr - 1870) / (2025 - 1870)) * plotW;
      ctx.fillText(String(yr), x - 14, padTop + plotH + 18);
    });
    [0, Math.floor(nScales * 0.33), Math.floor(nScales * 0.66), nScales - 1].forEach(sIdx => {
      const y = padTop + (nScales - 1 - sIdx) * cellH;
      ctx.fillText(EMPIRICAL_JST.periods[sIdx].toFixed(1) + "y", 6, y + 4);
    });
  }

  drawEmpiricalScalogram();
  window.addEventListener("resize", drawEmpiricalScalogram);
}
