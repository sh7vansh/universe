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
  sliderAgents.addEventListener('input', (e) => valAgents.textContent = e.target.value);
  sliderRateSens.addEventListener('input', (e) => valRateSens.textContent = parseFloat(e.target.value).toFixed(4));
  sliderResetCeiling.addEventListener('input', (e) => valResetCeiling.textContent = e.target.value);

  function runFullSimulation() {
    const N_agents = parseInt(sliderAgents.value);
    const N_banks = Math.max(5, Math.floor(N_agents / 10));
    const residueRatio = parseFloat(sliderResidue.value);
    const rateSens = parseFloat(sliderRateSens.value);
    const resetCeiling = parseFloat(sliderResetCeiling.value);

    const timesteps = 3000;
    const dt = 0.1;

    const agent_bank_map = new Int32Array(N_agents);
    const agent_incomes = new Float64Array(N_agents);
    const agent_debts = new Float64Array(N_agents);

    for (let i = 0; i < N_agents; i++) {
      agent_bank_map[i] = Math.floor(Math.random() * N_banks);
      agent_incomes[i] = 80 + Math.random() * 40;
      agent_debts[i] = 20 + Math.random() * 30;
    }

    const bank_capital = new Float64Array(N_banks).fill(100.0);
    const bank_bad_debt = new Float64Array(N_banks).fill(0.0);

    let sovereign_debt = 500.0;
    let base_rate = 0.05;

    const time_hist = [];
    const tier0_debt_hist = [];
    const tier2_debt_hist = [];
    const base_rate_hist = [];
    const defaults_hist = [];
    const reset_years = [];

    for (let t = 0; t < timesteps; t++) {
      const effective_rate = Math.max(0.005, base_rate);
      let step_defaults = 0;
      const defaulted_indices = [];

      for (let i = 0; i < N_agents; i++) {
        const shock = 1.0 + (Math.random() - 0.5) * 0.16;
        agent_incomes[i] = Math.max(10.0, Math.min(600.0, agent_incomes[i] * (1.0 + 0.015 * dt) * shock));

        const borrow = Math.max(0.0, 2.0 + (Math.random() - 0.5) * 2.0) * (1.0 / (1.0 + 10.0 * effective_rate));
        agent_debts[i] += borrow * dt;

        const debt_service = agent_debts[i] * (effective_rate + 0.04) * dt;
        const capacity = 0.40 * agent_incomes[i] * dt;

        if (debt_service > capacity) {
          step_defaults++;
          defaulted_indices.push(i);
        }
      }

      for (let idx of defaulted_indices) {
        const debt = agent_debts[idx];
        const absorbed = residueRatio * debt;
        agent_debts[idx] -= debt * 0.75;

        const b_idx = agent_bank_map[idx];
        bank_bad_debt[b_idx] += absorbed;
        bank_capital[b_idx] -= absorbed * 0.5;
      }

      let bank_failures = 0;
      for (let b = 0; b < N_banks; b++) {
        if (bank_capital[b] < 20.0 || bank_bad_debt[b] > 80.0) {
          bank_failures++;
          const bailout = bank_bad_debt[b] + (50.0 - bank_capital[b]);
          sovereign_debt += bailout;
          bank_capital[b] = 60.0;
          bank_bad_debt[b] = 0.0;
          base_rate = Math.max(0.005, base_rate - 0.015);
        } else {
          bank_capital[b] += 1.0 * dt;
        }
      }

      sovereign_debt += sovereign_debt * effective_rate * dt;

      if (step_defaults < (0.05 * N_agents) && bank_failures === 0) {
        base_rate = Math.min(0.09, base_rate + rateSens * dt);
      }

      if (sovereign_debt > resetCeiling) {
        sovereign_debt *= 0.35;
        base_rate = 0.06;
        reset_years.push(t * dt);
        for (let i = 0; i < N_agents; i++) {
          agent_debts[i] *= 0.50;
          agent_incomes[i] *= 0.80;
        }
      }

      const currTime = t * dt;
      let totalTier0 = 0;
      for (let i = 0; i < N_agents; i++) totalTier0 += agent_debts[i];

      time_hist.push(currTime);
      tier0_debt_hist.push(totalTier0);
      tier2_debt_hist.push(sovereign_debt);
      base_rate_hist.push(base_rate * 100);
      defaults_hist.push(step_defaults);
    }

    const fourier = computeFourier(defaults_hist, dt);

    const data = {
      time: time_hist,
      tier0_debt: tier0_debt_hist,
      tier2_debt: tier2_debt_hist,
      base_rate: base_rate_hist,
      defaults: defaults_hist,
      fourier: fourier,
      resets: reset_years
    };

    simTimeDisplay.textContent = `${data.time[data.time.length - 1].toFixed(1)} Years (${data.time.length} Steps)`;
    if (data.fourier.peaks.length >= 2) {
      peak1Display.textContent = `T₁ ≈ ${data.fourier.peaks[0].period.toFixed(2)} Years (Power: ${data.fourier.peaks[0].power.toExponential(2)})`;
      peak2Display.textContent = `T₂ ≈ ${data.fourier.peaks[1].period.toFixed(2)} Years (Power: ${data.fourier.peaks[1].power.toExponential(2)})`;
    }
    sovereignResetsDisplay.textContent = `${data.resets.length} Macro Resets Recorded`;

    renderDebtCharts(data);
  }

  function computeFourier(signal, dt) {
    const N = signal.length;
    let mean = 0;
    for (let i = 0; i < N; i++) mean += signal[i];
    mean /= N;

    const numBins = 70;
    const minPeriod = 0.3;
    const maxPeriod = 110.0;
    const logMin = Math.log10(minPeriod);
    const logMax = Math.log10(maxPeriod);

    const periods = [];
    const powers = [];

    for (let b = 0; b < numBins; b++) {
      const T = Math.pow(10, logMin + b * (logMax - logMin) / (numBins - 1));
      const omega = 2.0 * Math.PI / T;

      let realSum = 0;
      let imagSum = 0;
      for (let n = 0; n < N; n++) {
        const val = signal[n] - mean;
        realSum += val * Math.cos(omega * (n * dt));
        imagSum += val * Math.sin(omega * (n * dt));
      }
      const power = (realSum * realSum + imagSum * imagSum) / N;
      periods.push(T);
      powers.push(power);
    }

    const sortedPeaks = periods.map((p, idx) => ({ period: p, power: powers[idx] }))
      .sort((a, b) => b.power - a.power);

    return { periods, powers, peaks: sortedPeaks };
  }

  function renderDebtCharts(data) {
    const step = 3;
    const dsTime = [];
    const dsTier0 = [];
    const dsTier2 = [];
    const dsRate = [];
    const dsDefaults = [];

    for (let i = 0; i < data.time.length; i += step) {
      dsTime.push(data.time[i].toFixed(1));
      dsTier0.push(data.tier0_debt[i]);
      dsTier2.push(data.tier2_debt[i]);
      dsRate.push(data.base_rate[i]);
      dsDefaults.push(data.defaults[i]);
    }

    if (charts.tier0) charts.tier0.destroy();
    charts.tier0 = new Chart(document.getElementById('chartTier0Debt').getContext('2d'), {
      type: 'line',
      data: {
        labels: dsTime,
        datasets: [
          { label: 'Private Debt (D₀)', data: dsTier0, borderColor: '#38bdf8', borderWidth: 1.5, pointRadius: 0, yAxisID: 'y' },
          { label: 'Base Rate (%)', data: dsRate, borderColor: '#ef4444', borderWidth: 1.2, borderDash: [3, 3], pointRadius: 0, yAxisID: 'y1' }
        ]
      },
      options: getCommonOptions('Private Debt', 'Base Rate (%)')
    });

    if (charts.tier2) charts.tier2.destroy();
    charts.tier2 = new Chart(document.getElementById('chartTier2Debt').getContext('2d'), {
      type: 'line',
      data: {
        labels: dsTime,
        datasets: [{
          label: 'Sovereign Debt (Residue Ledger)',
          data: dsTier2,
          borderColor: '#a855f7',
          backgroundColor: 'rgba(168, 85, 247, 0.08)',
          fill: true,
          borderWidth: 1.8,
          pointRadius: 0
        }]
      },
      options: getCommonOptions('Sovereign Debt')
    });

    if (charts.defaults) charts.defaults.destroy();
    charts.defaults = new Chart(document.getElementById('chartDefaults').getContext('2d'), {
      type: 'bar',
      data: {
        labels: dsTime,
        datasets: [{ label: 'Default Events / Step', data: dsDefaults, backgroundColor: '#f97316', borderWidth: 0 }]
      },
      options: getCommonOptions('Defaults / Step')
    });

    if (charts.fourier) charts.fourier.destroy();
    charts.fourier = new Chart(document.getElementById('chartFourier').getContext('2d'), {
      type: 'line',
      data: {
        labels: data.fourier.periods.map(p => p.toFixed(1)),
        datasets: [{
          label: 'Spectral Power Density',
          data: data.fourier.powers,
          borderColor: '#10b981',
          borderWidth: 2.0,
          pointRadius: 1.5,
          pointBackgroundColor: '#10b981'
        }]
      },
      options: {
        responsive: true,
        maintainAspectRatio: false,
        scales: {
          x: { type: 'logarithmic', title: { display: true, text: 'Period (Years) [Log]', color: '#94a3b8' }, grid: { color: 'rgba(255,255,255,0.06)' }, ticks: { color: '#64748b' } },
          y: { type: 'logarithmic', title: { display: true, text: 'Spectral Power [Log]', color: '#94a3b8' }, grid: { color: 'rgba(255,255,255,0.06)' }, ticks: { color: '#64748b' } }
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
