'use strict';

let downloadDailyLog = () => {};
let uploadDailyLog = () => {};

(() => {
	const urlParams = new URLSearchParams(window.location.search);
	const dualMode = urlParams.has('dual');
	const withChecksum = urlParams.has('cs');
	const Connection = __ble_mx_api.ConnectionExt;
	const str2Uint8Array = __ble_mx_api.str2Uint8Array;
	const compressTag = __ble_mx_api.COMPRESS_TAG;
	const decompress = __ble_mx_api.decompress;

	const packetBytes = 408;
	const legacyPacketBytes = 404;
	const packetHeaderBytes = 8;
	const legacyPacketHeaderBytes = 4;
	const samplesPerPacket = 100;
	const nominalBleBytesPerSecond = 30000;
	const nominalPacketIntervalMs = (packetBytes / nominalBleBytesPerSecond) * 1000;
	let sampleIntervalMs = nominalPacketIntervalMs / samplesPerPacket;
	const connectionTimeoutMs = 2000;
	const samplesPerSummaryBlock = 256;
	const samplesPerCoarseBlock = samplesPerSummaryBlock * 256;
	const summarySegmentSize = 8192;
	const segmentSize = 32768;
	const bufferSize = 360000;
	const bufferPeriodMs = 10000;
	const shuntOhms = 0.00025;
	const busLsb = 0.00125;
	const shuntLsb = 0.0000025;
	const voltageColor = '#35d4ff';
	const currentColor = '#ffbd45';

	const connectButton = document.getElementById('bt-btn');
	const transportSelect = document.getElementById('transport-select');
	const fullscreenButton = document.getElementById('fullscreen-btn');
	const suspendButton = document.getElementById('bt-btn2');
	const txForm = document.getElementById('tx-form');
	const txInput = document.getElementById('tx-msg');
	const rxOutput = document.getElementById('rx-msg');
	const statusOutput = document.getElementById('label1');
	const chartInfo = document.getElementById('chart-info');
	const mainCanvas = document.getElementById('mainChart');
	const navCanvas = document.getElementById('navChart');
	const channelSelect = document.getElementById('channel-select');
	const chartModeSelect = document.getElementById('chart-mode');
	const timeDivSelect = document.getElementById('time-div');
	const voltageDivSelect = document.getElementById('voltage-div');
	const currentDivSelect = document.getElementById('current-div');
	const readout = document.getElementById('readout');
	const readoutVoltage = document.getElementById('readout-voltage');
	const readoutCurrent = document.getElementById('readout-current');
	const readoutVoltageToggle = document.getElementById('readout-v-toggle');
	const readoutCurrentToggle = document.getElementById('readout-i-toggle');
	const connectionAlert = document.getElementById('connection-alert');
	const connectionAlertMessage = document.getElementById('connection-alert-message');
	const connectionCancelButton = document.getElementById('connection-cancel');
	const connectionReconnectButton = document.getElementById('connection-reconnect');
	const mainContext = mainCanvas.getContext('2d');
	const navContext = navCanvas.getContext('2d');
	const settings = loadSettings();

	const series = {
		samples: [],
		vMin: [],
		vMax: [],
		iMin: [],
		iMax: [],
		vCoarseMin: [],
		vCoarseMax: [],
		iCoarseMin: [],
		iCoarseMax: []
	};

	let db = null;
	let activeBuffer = new Uint8Array(bufferSize);
	let standbyBuffer = new Uint8Array(bufferSize);
	let writeIndex = 0;
	let bufferTimer = null;
	let recordStartTime = 0;
	let btConnection = null;
	let activeTransport = null;
	let selectedSerialPort = null;
	let usbPort = null;
	let usbReader = null;
	let usbWriter = null;
	let usbReceiveBuffer = new Uint8Array(0);
	let storageReady = false;
	let suspended = false;
	let packetCount = 0;
	let receivedPacketCount = 0;
	let totalBytes = 0;
	let firstPacketNumber = null;
	let channel = settings.channel;
	let chartMode = settings.chartMode;
	let timePerDivisionSeconds = settings.timePerDivisionSeconds;
	let voltagePerDivision = settings.voltagePerDivision;
	let currentPerDivision = settings.currentPerDivision;
	let overlayShowVoltage = settings.overlayShowVoltage;
	let overlayShowCurrent = settings.overlayShowCurrent;
	let readoutPosition = settings.readoutPosition;
	let readoutFontSize = settings.readoutFontSize;
	let latestAverageVoltage = null;
	let latestAverageCurrent = null;
	const recentReadoutSamples = [];
	const timingIntervals = [];
	let overlayDrag = null;
	let overlayHighlightTimer = null;
	let showCursors = settings.showCursors;
	let cursorA = settings.cursorA;
	let cursorB = settings.cursorB;
	let vZeroOffset = settings.vZeroOffset;
	let iZeroOffset = settings.iZeroOffset;
	let vYZoom = settings.vYZoom;
	let iYZoom = settings.iYZoom;
	let viewStart = 0;
	let viewEnd = 0;
	let viewStartTime = 0;
	let renderPending = false;
	let navigatorNeedsRender = true;
	let lastRender = 0;
	let lastChartInfoUpdate = 0;
	let lastNavigatorRender = 0;
	let mainDrag = null;
	let navDrag = null;
	const mainPointers = new Map();
	let chartPinch = null;
	let wakeLock = null;
	let wakeLockRequestPending = false;
	let wakeLockStatus = 'Screen may sleep';
	let selectedDevice = null;
	let lastPacketArrivalAt = null;
	let receivedPacketSinceConnection = false;
	let lastTimingPacketNumber = null;
	let lastSourceTimestampUs = null;
	let timingDeviationMs = 0;
	let timingSampleCount = 0;
	let timingCalibrated = false;
	let connectionAlertDismissed = false;
	let audioContext = null;
	let connectionAlertSoundTimer = null;

	function loadSettings() {
		const defaults = {
			channel: 'V',
			chartMode: 'history',
			timePerDivisionSeconds: 0.001,
			voltagePerDivision: 5,
			currentPerDivision: 0.5,
			overlayShowVoltage: true,
			overlayShowCurrent: true,
			vZeroOffset: 0.5,
			iZeroOffset: 0.5,
			vYZoom: 1,
			iYZoom: 1,
			showCursors: false,
			cursorA: 0.3,
			cursorB: 0.7,
			readoutPosition: { x: 0.04, y: 0.1 },
			readoutFontSize: 18
		};

		try {
			const stored = JSON.parse(localStorage.getItem('bleRecorderSettings') || '{}');
			return {
				channel: ['V', 'I', 'VI'].includes(stored.channel) ? stored.channel : defaults.channel,
				chartMode: ['history', 'scope'].includes(stored.chartMode) ? stored.chartMode : defaults.chartMode,
				timePerDivisionSeconds: Array.from(document.getElementById('time-div').options)
					.map((option) => Number(option.value))
					.includes(Number(stored.timePerDivisionSeconds))
					? Number(stored.timePerDivisionSeconds)
					: defaults.timePerDivisionSeconds,
				voltagePerDivision: Array.from(document.getElementById('voltage-div').options)
					.map((option) => Number(option.value))
					.includes(Number(stored.voltagePerDivision))
					? Number(stored.voltagePerDivision)
					: defaults.voltagePerDivision,
				currentPerDivision: Array.from(document.getElementById('current-div').options)
					.map((option) => Number(option.value))
					.includes(Number(stored.currentPerDivision))
					? Number(stored.currentPerDivision)
					: defaults.currentPerDivision,
				overlayShowVoltage: typeof stored.overlayShowVoltage === 'boolean' ? stored.overlayShowVoltage : defaults.overlayShowVoltage,
				overlayShowCurrent: typeof stored.overlayShowCurrent === 'boolean' ? stored.overlayShowCurrent : defaults.overlayShowCurrent,
				vZeroOffset: Number.isFinite(stored.vZeroOffset)
					? Math.max(-4, Math.min(4, stored.vZeroOffset))
					: 0.5,
				iZeroOffset: Number.isFinite(stored.iZeroOffset)
					? Math.max(-4, Math.min(4, stored.iZeroOffset))
					: 0.5,
				vYZoom: Number.isFinite(stored.vYZoom)
					? Math.max(0.1, Math.min(100, stored.vYZoom))
					: 1,
				iYZoom: Number.isFinite(stored.iYZoom)
					? Math.max(0.1, Math.min(100, stored.iYZoom))
					: 1,
				showCursors: typeof stored.showCursors === 'boolean' ? stored.showCursors : false,
				cursorA: Number.isFinite(stored.cursorA) ? Math.max(0, Math.min(1, stored.cursorA)) : 0.3,
				cursorB: Number.isFinite(stored.cursorB) ? Math.max(0, Math.min(1, stored.cursorB)) : 0.7,
				readoutPosition: stored.readoutPosition &&
					Number.isFinite(stored.readoutPosition.x) &&
					Number.isFinite(stored.readoutPosition.y)
					? {
						x: Math.max(0, Math.min(0.95, stored.readoutPosition.x)),
						y: Math.max(0, Math.min(0.9, stored.readoutPosition.y))
					}
					: defaults.readoutPosition,
				readoutFontSize: Number.isFinite(stored.readoutFontSize)
					? Math.max(10, Math.min(64, stored.readoutFontSize))
					: defaults.readoutFontSize
			};
		} catch (error) {
			console.warn('Could not load saved recorder settings:', error);
			return defaults;
		}
	}

	function saveSettings() {
		try {
			localStorage.setItem('bleRecorderSettings', JSON.stringify({
				channel,
				chartMode,
				timePerDivisionSeconds,
				voltagePerDivision,
				currentPerDivision,
				overlayShowVoltage,
				overlayShowCurrent,
				vZeroOffset,
				iZeroOffset,
				vYZoom,
				iYZoom,
				showCursors,
				cursorA,
				cursorB,
				readoutPosition,
				readoutFontSize
			}));
		} catch (error) {
			console.error('Could not save recorder settings:', error);
			setStatus(`Settings could not be saved: ${error.message}`);
		}
	}

	function setStatus(message) {
		rxOutput.textContent = message;
	}

	function applyReadoutSettings() {
		readout.style.left = `${readoutPosition.x * 100}%`;
		readout.style.top = `${readoutPosition.y * 100}%`;
		readout.style.fontSize = `${readoutFontSize}px`;
		readoutVoltage.hidden = !overlayShowVoltage;
		readoutCurrent.hidden = !overlayShowCurrent;
		readout.hidden = !overlayShowVoltage && !overlayShowCurrent;
		keepReadoutInBounds();
	}

	function keepReadoutInBounds() {
		const panel = readout.parentElement.getBoundingClientRect();
		const bounds = readout.getBoundingClientRect();
		if (panel.width === 0 || panel.height === 0) return;
		const maxX = Math.max(0, panel.width - bounds.width);
		const maxY = Math.max(0, panel.height - bounds.height);
		const left = Math.max(0, Math.min(maxX, readoutPosition.x * panel.width));
		const top = Math.max(0, Math.min(maxY, readoutPosition.y * panel.height));
		readoutPosition = { x: left / panel.width, y: top / panel.height };
		readout.style.left = `${readoutPosition.x * 100}%`;
		readout.style.top = `${readoutPosition.y * 100}%`;
	}

	function updateReadout() {
		const cutoff = performance.now() - 300;
		while (recentReadoutSamples.length > 0 && recentReadoutSamples[0].time < cutoff) {
			recentReadoutSamples.shift();
		}
		if (recentReadoutSamples.length === 0) {
			if (latestAverageVoltage === null || latestAverageCurrent === null) {
				readoutVoltage.textContent = '---.--- V';
				readoutCurrent.textContent = '---.--- A';
			}
			return;
		}
		let voltageSum = 0;
		let currentSum = 0;
		let sampleCount = 0;
		for (const sample of recentReadoutSamples) {
			voltageSum += sample.voltage * sample.count;
			currentSum += sample.current * sample.count;
			sampleCount += sample.count;
		}
		readoutVoltage.textContent = `${(voltageSum / sampleCount).toFixed(3)} V`;
		readoutCurrent.textContent = `${(currentSum / sampleCount).toFixed(3)} A`;
	}

	function showReadoutSelection() {
		readout.classList.add('selected');
		if (overlayHighlightTimer !== null) window.clearTimeout(overlayHighlightTimer);
		overlayHighlightTimer = window.setTimeout(() => {
			readout.classList.remove('selected');
			overlayHighlightTimer = null;
		}, 3000);
	}

	function onReadoutPointerDown(event) {
		if (event.button !== 0) return;
		event.preventDefault();
		readout.setPointerCapture(event.pointerId);
		showReadoutSelection();
		if (event.target.classList.contains('readout-resize')) {
			overlayDrag = {
				type: 'resize',
				x: event.clientX,
				y: event.clientY,
				fontSize: readoutFontSize
			};
		} else {
			overlayDrag = {
				type: 'move',
				x: event.clientX,
				y: event.clientY,
				position: { ...readoutPosition }
			};
		}
	}

	function onReadoutPointerMove(event) {
		if (!overlayDrag) return;
		const panel = readout.parentElement.getBoundingClientRect();
		if (overlayDrag.type === 'resize') {
			const delta = Math.max(event.clientX - overlayDrag.x, event.clientY - overlayDrag.y);
			readoutFontSize = Math.max(10, Math.min(64, overlayDrag.fontSize + delta * 0.12));
			readout.style.fontSize = `${readoutFontSize}px`;
		} else {
			const readoutBounds = readout.getBoundingClientRect();
			const maxX = Math.max(0, panel.width - readoutBounds.width);
			const maxY = Math.max(0, panel.height - readoutBounds.height);
			readoutPosition = {
				x: maxX > 0
					? Math.max(0, Math.min(maxX / panel.width, (overlayDrag.position.x * panel.width + event.clientX - overlayDrag.x) / panel.width))
					: 0,
				y: maxY > 0
					? Math.max(0, Math.min(maxY / panel.height, (overlayDrag.position.y * panel.height + event.clientY - overlayDrag.y) / panel.height))
					: 0
			};
			readout.style.left = `${readoutPosition.x * 100}%`;
			readout.style.top = `${readoutPosition.y * 100}%`;
		}
		showReadoutSelection();
	}

	function onReadoutPointerUp() {
		if (!overlayDrag) return;
		overlayDrag = null;
		saveSettings();
	}

	function initPage() {
		channelSelect.value = channel;
		chartModeSelect.value = chartMode;
		timeDivSelect.value = String(timePerDivisionSeconds);
		voltageDivSelect.value = String(voltagePerDivision);
		currentDivSelect.value = String(currentPerDivision);
		readoutVoltageToggle.checked = overlayShowVoltage;
		readoutCurrentToggle.checked = overlayShowCurrent;
		const cursorButton = document.getElementById('cursor-btn');
		cursorButton.textContent = `Cursors: ${showCursors ? 'On' : 'Off'}`;
		cursorButton.setAttribute('aria-pressed', String(showCursors));
		readout.addEventListener('pointerdown', onReadoutPointerDown);
		readout.addEventListener('pointermove', onReadoutPointerMove);
		readout.addEventListener('pointerup', onReadoutPointerUp);
		readout.addEventListener('pointercancel', onReadoutPointerUp);
		connectButton.addEventListener('click', onConnectClick);
		transportSelect.addEventListener('change', updateConnectionControls);
		fullscreenButton.addEventListener('click', toggleFullscreen);
		suspendButton.addEventListener('click', () => setSuspended(!suspended));
		txForm.addEventListener('submit', onSendCommand);
		document.getElementById('download-btn').addEventListener('click', downloadDailyLog);
		document.getElementById('upload-btn').addEventListener('click', uploadDailyLog);
		document.getElementById('clear-btn').addEventListener('click', clearRecording);
		document.getElementById('cursor-btn').addEventListener('click', toggleCursors);
		connectionCancelButton.addEventListener('click', dismissConnectionAlert);
		connectionReconnectButton.addEventListener('click', reconnectSelectedDevice);
		channelSelect.addEventListener('change', (event) => {
			channel = event.target.value;
			saveSettings();
			requestRender(true);
		});
		chartModeSelect.addEventListener('change', (event) => {
			chartMode = event.target.value;
			if (chartMode === 'scope') scrollToScopeWindow();
			saveSettings();
			requestRender(true);
		});
		timeDivSelect.addEventListener('change', (event) => {
			timePerDivisionSeconds = Number(event.target.value);
			if (chartMode === 'scope') scrollToScopeWindow();
			saveSettings();
			requestRender(true);
		});
		voltageDivSelect.addEventListener('change', (event) => {
			voltagePerDivision = Number(event.target.value);
			requestRender(true);
			saveSettings();
		});
		currentDivSelect.addEventListener('change', (event) => {
			currentPerDivision = Number(event.target.value);
			requestRender(true);
			saveSettings();
		});
		readoutVoltageToggle.addEventListener('change', () => {
			overlayShowVoltage = readoutVoltageToggle.checked;
			applyReadoutSettings();
			saveSettings();
		});
		readoutCurrentToggle.addEventListener('change', () => {
			overlayShowCurrent = readoutCurrentToggle.checked;
			applyReadoutSettings();
			saveSettings();
		});

		mainCanvas.addEventListener('pointerdown', onMainPointerDown);
		mainCanvas.addEventListener('pointermove', onMainPointerMove);
		mainCanvas.addEventListener('pointerup', onMainPointerUp);
		mainCanvas.addEventListener('pointercancel', onMainPointerUp);
		mainCanvas.addEventListener('wheel', onMainWheel, { passive: false });
		navCanvas.addEventListener('pointerdown', onNavPointerDown);
		navCanvas.addEventListener('pointermove', onNavPointerMove);
		navCanvas.addEventListener('pointerup', onNavPointerUp);
		navCanvas.addEventListener('pointercancel', onNavPointerUp);
		window.addEventListener('resize', () => {
			applyReadoutSettings();
			saveSettings();
			requestRender(true);
		});
		document.addEventListener('fullscreenchange', updateFullscreenButton);
		document.addEventListener('visibilitychange', onVisibilityChange);
		window.setInterval(updateReadout, 300);
		window.setInterval(checkConnectionHealth, 500);
		applyReadoutSettings();

		if (navigator.bluetooth) {
			btConnection = new Connection(receiveFrame, dualMode);
		}
		if (!navigator.bluetooth && navigator.serial) transportSelect.value = 'usb';
		updateConnectionControls();
		if (!navigator.bluetooth && !navigator.serial) {
			setStatus('Bluetooth and USB Serial are not supported by this browser. Use Chrome or Edge.');
		}
		requestScreenWakeLock();
		openDatabase();
		requestRender(true);
	}

	function updateFullscreenButton() {
		const isFullscreen = Boolean(document.fullscreenElement);
		fullscreenButton.textContent = isFullscreen ? 'Exit full screen' : 'Full screen';
		fullscreenButton.setAttribute('aria-pressed', String(isFullscreen));
		if (!isFullscreen && screen.orientation && screen.orientation.unlock) {
			screen.orientation.unlock();
		}
	}

	function toggleFullscreen() {
		requestScreenWakeLock();
		if (document.fullscreenElement) {
			document.exitFullscreen().catch((error) => {
				console.error('Could not exit full screen:', error);
				setStatus(`Full-screen error: ${error.message}`);
			});
			return;
		}
		if (!document.documentElement.requestFullscreen) {
			setStatus('Full screen is not supported by this browser');
			return;
		}
		document.documentElement.requestFullscreen().then(() => {
			if (screen.orientation && screen.orientation.lock) {
				return screen.orientation.lock('landscape').catch((error) => {
					console.info('Landscape lock was not accepted:', error);
				});
			}
		}).catch((error) => {
			console.error('Could not enter full screen:', error);
			setStatus(`Full-screen error: ${error.message}`);
		});
	}

	async function requestScreenWakeLock() {
		if (wakeLock || wakeLockRequestPending) return;
		if (!navigator.wakeLock || document.visibilityState !== 'visible') {
			wakeLockStatus = navigator.wakeLock ? 'Screen may sleep while hidden' : 'Wake lock unavailable';
			updateStatus();
			return;
		}
		wakeLockRequestPending = true;
		try {
			wakeLock = await navigator.wakeLock.request('screen');
			wakeLockStatus = 'Screen awake';
			wakeLock.addEventListener('release', () => {
				wakeLock = null;
				wakeLockStatus = 'Screen may sleep';
				updateStatus();
				if (document.visibilityState === 'visible') {
					window.setTimeout(requestScreenWakeLock, 0);
				}
			}, { once: true });
			updateStatus();
		} catch (error) {
			wakeLock = null;
			wakeLockStatus = 'Wake lock unavailable';
			console.warn('Could not keep the screen awake:', error);
			updateStatus();
		} finally {
			wakeLockRequestPending = false;
		}
	}

	function onVisibilityChange() {
		if (document.visibilityState === 'visible' && !wakeLock) requestScreenWakeLock();
	}

	function openDatabase() {
		const request = indexedDB.open('BleRawProductionStorage', 1);
		request.onupgradeneeded = (event) => {
			const database = event.target.result;
			if (!database.objectStoreNames.contains('chunks')) {
				database.createObjectStore('chunks', { autoIncrement: true });
			}
		};
		request.onsuccess = (event) => {
			db = event.target.result;
			db.onversionchange = () => db.close();
			bufferTimer = window.setInterval(switchAndFlushBuffer, bufferPeriodMs);
			storageReady = true;
			updateConnectionControls();
			setStatus('Storage ready · press Connect');
			updateStatus();
		};
		request.onerror = () => {
			console.error('IndexedDB initialization failed:', request.error);
			setStatus('Error: could not open recording storage');
		};
	}

	function updateConnectionControls() {
		const supported = transportSelect.value === 'usb'
			? Boolean(navigator.serial)
			: Boolean(navigator.bluetooth && btConnection);
		connectButton.disabled = !storageReady || !supported || activeTransport !== null;
		transportSelect.disabled = activeTransport !== null;
	}

	function onConnectClick() {
		requestScreenWakeLock();
		prepareAudio();
		if (transportSelect.value === 'usb') {
			connectUSB();
			return;
		}
		if (!btConnection || btConnection.is_connected()) return;

		let deviceRequest;
		try {
			deviceRequest = navigator.bluetooth.requestDevice({
				filters: [{ services: [Connection.bt_svc_id] }]
			});
		} catch (error) {
			console.error('Bluetooth device selection failed:', error);
			setStatus(`Bluetooth error: ${error.message}`);
			return;
		}

		connectButton.disabled = true;
		transportSelect.disabled = true;
		setStatus('Bluetooth: searching for devices…');
		deviceRequest.then((device) => {
			selectedDevice = device;
			activeTransport = 'ble';
			setStatus(`Bluetooth: connecting to ${device.name || 'ESP32'}…`);
			btConnection.connect(device, onConnected, onDisconnected);
		}).catch((error) => {
			console.error('Bluetooth device selection failed:', error);
			activeTransport = null;
			updateConnectionControls();
			setStatus(`Bluetooth error: ${error.message}`);
		});
	}

	function onConnected(device) {
		activeTransport = 'ble';
		selectedDevice = device;
		lastPacketArrivalAt = performance.now();
		receivedPacketSinceConnection = false;
		if (!timingCalibrated) {
			lastTimingPacketNumber = null;
			lastSourceTimestampUs = null;
			timingIntervals.length = 0;
			timingSampleCount = 0;
			timingDeviationMs = 0;
			sampleIntervalMs = nominalPacketIntervalMs / samplesPerPacket;
		}
		dismissConnectionAlert(false);
		connectButton.disabled = false;
		connectButton.textContent = 'Connected';
		suspendButton.disabled = false;
		const canWrite = !btConnection.is_redonly();
		txForm.classList.toggle('active', canWrite);
		txInput.disabled = !canWrite;
		txForm.querySelector('button').disabled = !canWrite;
		updateConnectionControls();
		setStatus(canWrite
			? `Connected: ${device.name || 'ESP32'}`
			: 'BLE is read-only. For DUAL_CHAR, open the page with ?dual');

		if (document.documentElement.requestFullscreen && !document.fullscreenElement) {
			document.documentElement.requestFullscreen().then(() => {
				if (screen.orientation && screen.orientation.lock) {
					return screen.orientation.lock('landscape').catch((error) => {
						console.info('Landscape lock was not accepted:', error);
					});
				}
			}).catch((error) => {
				console.info('Fullscreen request was not accepted:', error);
			});
		}
	}

	function onDisconnected(device) {
		activeTransport = null;
		connectButton.textContent = 'Connect';
		suspendButton.disabled = true;
		txInput.disabled = true;
		txForm.querySelector('button').disabled = true;
		updateConnectionControls();
		setStatus(`Disconnected: ${device.name || 'ESP32'}`);
		if (receivedPacketSinceConnection) {
			showConnectionAlert('Connection was lost. Reconnect to resume receiving data.');
		}
	}

	async function connectUSB(port = null) {
		if (!navigator.serial) {
			setStatus('USB Serial is not supported. Use Chrome or Edge on a supported page.');
			return;
		}

		connectButton.disabled = true;
		try {
			transportSelect.disabled = true;
			selectedSerialPort = port || await navigator.serial.requestPort();
			usbPort = selectedSerialPort;
			await usbPort.open({ baudRate: 921600, bufferSize: 8192 });
			usbReader = usbPort.readable.getReader();
			usbWriter = usbPort.writable.getWriter();
			activeTransport = 'usb';
			usbReceiveBuffer = new Uint8Array(0);
			lastPacketArrivalAt = performance.now();
			receivedPacketSinceConnection = false;
			dismissConnectionAlert(false);
			connectButton.textContent = 'Connected (USB)';
			suspendButton.disabled = false;
			txInput.disabled = false;
			txForm.querySelector('button').disabled = false;
			txForm.classList.add('active');
			updateConnectionControls();
			setStatus('USB Serial connected');
			readUSBStream(usbReader);
		} catch (error) {
			console.error('USB Serial connection failed:', error);
			activeTransport = null;
			if (usbReader) {
				try {
					await usbReader.cancel();
					usbReader.releaseLock();
				} catch (cleanupError) {
					console.warn('Could not release the failed USB Serial reader:', cleanupError);
				}
			}
			if (usbWriter) {
				try {
					usbWriter.releaseLock();
				} catch (cleanupError) {
					console.warn('Could not release the failed USB Serial writer:', cleanupError);
				}
			}
			if (usbPort) {
				try {
					await usbPort.close();
				} catch (cleanupError) {
					console.warn('Could not close the failed USB Serial port:', cleanupError);
				}
			}
			usbPort = null;
			usbReader = null;
			usbWriter = null;
			connectButton.textContent = 'Connect';
			updateConnectionControls();
			setStatus(`USB Serial error: ${error.message}`);
			if (!connectionAlert.hidden) connectionReconnectButton.disabled = false;
		}
	}

	async function readUSBStream(reader) {
		let readError = null;
		try {
			while (true) {
				const { value, done } = await reader.read();
				if (done) break;
				if (value && value.length) receiveUSBBytes(value);
			}
		} catch (error) {
			readError = error;
			console.warn('USB Serial read ended:', error);
		} finally {
			if (usbReader === reader) usbReader = null;
			try {
				reader.releaseLock();
			} catch (error) {
				console.warn('Could not release the USB Serial reader:', error);
			}
			if (activeTransport !== 'usb') return;
			activeTransport = null;
			if (usbWriter) {
				try {
					usbWriter.releaseLock();
				} catch (error) {
					console.warn('Could not release the USB Serial writer:', error);
				}
				usbWriter = null;
			}
			if (usbPort) {
				const disconnectedPort = usbPort;
				usbPort = null;
				try {
					await disconnectedPort.close();
				} catch (error) {
					console.warn('Could not close the disconnected USB Serial port:', error);
				}
			}
			connectButton.textContent = 'Connect';
			suspendButton.disabled = true;
			txInput.disabled = true;
			txForm.querySelector('button').disabled = true;
			updateConnectionControls();
			setStatus(readError ? `USB Serial disconnected: ${readError.message}` : 'USB Serial disconnected');
			if (receivedPacketSinceConnection) {
				showConnectionAlert('USB connection was lost. Reconnect to resume receiving data.');
			}
		}
	}

	function receiveUSBBytes(chunk) {
		const combined = new Uint8Array(usbReceiveBuffer.length + chunk.length);
		combined.set(usbReceiveBuffer);
		combined.set(chunk, usbReceiveBuffer.length);
		usbReceiveBuffer = combined;
		const magic = [0x56, 0x41, 0x52, 0x31];
		const frameSize = packetBytes + 6;

		while (usbReceiveBuffer.length >= magic.length) {
			let marker = -1;
			for (let i = 0; i <= usbReceiveBuffer.length - magic.length; i++) {
				if (magic.every((byte, offset) => usbReceiveBuffer[i + offset] === byte)) {
					marker = i;
					break;
				}
			}
			if (marker < 0) {
				usbReceiveBuffer = usbReceiveBuffer.slice(-3);
				return;
			}
			if (marker > 0) usbReceiveBuffer = usbReceiveBuffer.slice(marker);
			if (usbReceiveBuffer.length < frameSize) return;

			const payload = usbReceiveBuffer.subarray(magic.length, magic.length + packetBytes);
			const expectedCrc = (usbReceiveBuffer[frameSize - 2] << 8) | usbReceiveBuffer[frameSize - 1];
			if (crc16Ccitt(payload) !== expectedCrc) {
				usbReceiveBuffer = usbReceiveBuffer.slice(1);
				continue;
			}
			const packet = payload.slice();
			usbReceiveBuffer = usbReceiveBuffer.slice(frameSize);
			receiveFrame(new DataView(packet.buffer), true);
		}
	}

	function crc16Ccitt(bytes) {
		let crc = 0xffff;
		for (const byte of bytes) {
			crc ^= byte << 8;
			for (let bit = 0; bit < 8; bit++) {
				crc = (crc & 0x8000) ? ((crc << 1) ^ 0x1021) & 0xffff : (crc << 1) & 0xffff;
			}
		}
		return crc;
	}

	function prepareAudio() {
		const AudioContextClass = window.AudioContext || window.webkitAudioContext;
		if (!AudioContextClass) return;
		try {
			if (!audioContext) audioContext = new AudioContextClass();
			if (audioContext.state === 'suspended') {
				audioContext.resume().catch((error) => {
					console.warn('Could not enable connection alert sound:', error);
				});
			}
		} catch (error) {
			console.warn('Could not prepare connection alert sound:', error);
		}
	}

	function playConnectionAlertSound() {
		if (!audioContext || audioContext.state !== 'running') return;
		try {
			const oscillator = audioContext.createOscillator();
			const gain = audioContext.createGain();
			oscillator.type = 'sine';
			oscillator.frequency.value = 880;
			gain.gain.setValueAtTime(0.12, audioContext.currentTime);
			gain.gain.exponentialRampToValueAtTime(0.001, audioContext.currentTime + 0.45);
			oscillator.connect(gain);
			gain.connect(audioContext.destination);
			oscillator.start();
			oscillator.stop(audioContext.currentTime + 0.45);
		} catch (error) {
			console.warn('Could not play connection alert sound:', error);
		}
	}

	function showConnectionAlert(message) {
		if (connectionAlertDismissed || !connectionAlert.hidden) return;
		connectionAlertMessage.textContent = message;
		connectionAlert.hidden = false;
		connectionReconnectButton.disabled = !(selectedDevice || selectedSerialPort);
		playConnectionAlertSound();
		connectionAlertSoundTimer = window.setInterval(() => {
			if (!connectionAlert.hidden && !connectionAlertDismissed) playConnectionAlertSound();
		}, 5000);
	}

	function dismissConnectionAlert(markDismissed = true) {
		connectionAlert.hidden = true;
		if (connectionAlertSoundTimer !== null) {
			window.clearInterval(connectionAlertSoundTimer);
			connectionAlertSoundTimer = null;
		}
		if (markDismissed) {
			connectionAlertDismissed = true;
		} else {
			connectionAlertDismissed = false;
		}
	}

	function checkConnectionHealth() {
		const isConnected = activeTransport === 'ble'
			? Boolean(btConnection && btConnection.is_connected())
			: activeTransport === 'usb' && Boolean(usbReader);
		if (receivedPacketSinceConnection && isConnected &&
			lastPacketArrivalAt !== null &&
			performance.now() - lastPacketArrivalAt >= connectionTimeoutMs) {
			showConnectionAlert('No data has been received for 2 seconds. Check the device and reconnect.');
		}
	}

	function reconnectSelectedDevice() {
		if (transportSelect.value === 'usb') {
			connectionReconnectButton.disabled = true;
			connectionAlertMessage.textContent = 'Reconnecting to USB Serial…';
			connectionAlertDismissed = false;
			if (connectionAlertSoundTimer !== null) {
				window.clearInterval(connectionAlertSoundTimer);
				connectionAlertSoundTimer = null;
			}
			connectUSB(selectedSerialPort);
			return;
		}
		if (!selectedDevice || !btConnection) {
			connectionReconnectButton.disabled = true;
			connectionAlertMessage.textContent = 'Reconnect is unavailable. Use Connect to select the device again.';
			return;
		}
		connectionReconnectButton.disabled = true;
		connectionAlertMessage.textContent = `Reconnecting to ${selectedDevice.name || 'ESP32'}…`;
		connectionAlertDismissed = false;
		if (connectionAlertSoundTimer !== null) {
			window.clearInterval(connectionAlertSoundTimer);
			connectionAlertSoundTimer = null;
		}
		try {
			if (selectedDevice.gatt.connected) selectedDevice.gatt.disconnect();
			window.setTimeout(() => {
				btConnection.connect(selectedDevice, onConnected, onDisconnected);
			}, 300);
		} catch (error) {
			console.error('Could not reconnect to Bluetooth device:', error);
			connectionReconnectButton.disabled = false;
			connectionAlertMessage.textContent = `Reconnect failed: ${error.message}`;
		}
	}

	function onSendCommand(event) {
		event.preventDefault();
		const command = `${txInput.value.trim()}\r`;
		if (activeTransport === 'usb' && usbWriter) {
			usbWriter.write(new TextEncoder().encode(command)).then(() => {
				setStatus(`Command sent over USB: ${txInput.value.trim()}`);
			}).catch((error) => {
				console.error('USB Serial command write failed:', error);
				setStatus(`USB Serial write error: ${error.message}`);
			});
			return;
		}
		if (!btConnection || !btConnection.is_connected()) {
			setStatus('Connect to ESP32 first');
			return;
		}

		btConnection.write(str2Uint8Array(command), false, false);
		setStatus(`Command sent over BLE: ${txInput.value.trim()}`);
	}

	function setSuspended(value) {
		suspended = value;
		suspendButton.textContent = value ? 'Resume' : 'Suspend';
		suspendButton.setAttribute('aria-pressed', String(value));
		if (!value) {
			setStatus('Display resumed');
			requestRender(true);
		} else {
			setStatus('Display paused; recording continues');
		}
	}

	function receiveFrame(data, isBinary = false) {
		const receivedAt = performance.now();
		saveRawBytes(data);
		if (recordStartTime === 0) {
			recordStartTime = Date.now();
			viewStartTime = recordStartTime;
		}

		const length = data.byteLength;
		if (length === 0) return;
		totalBytes += length;

		if (withChecksum && data.getUint8(length - 1) === compressTag) {
			decompress(new DataView(data.buffer, data.byteOffset, length - 1))
				.then((decoded) => processFrame(decoded, isBinary, receivedAt))
				.catch((error) => {
					console.error('Failed to decompress BLE frame:', error);
					setStatus(`Decompression error: ${error.message}`);
				});
			updateStatus();
			return;
		}

		processFrame(data, isBinary, receivedAt);
		updateStatus();
	}

	function processFrame(data, isBinary, receivedAt) {
		const headerBytes = data.byteLength === packetBytes
			? packetHeaderBytes
			: data.byteLength === legacyPacketBytes ? legacyPacketHeaderBytes : 0;
		if (headerBytes === 0) {
			setStatus(`Unsupported packet size (${data.byteLength} bytes); chart not updated`);
			return;
		}

		const packetNumber = data.getUint32(0, false);
		const sourceTimestampUs = headerBytes === packetHeaderBytes ? data.getUint32(4, false) : null;
		if (sourceTimestampUs !== null) updateSampleInterval(packetNumber, sourceTimestampUs);
		receivedPacketSinceConnection = true;
		lastPacketArrivalAt = receivedAt;
		connectionAlertDismissed = false;
		dismissConnectionAlert(false);
		if (firstPacketNumber === null) firstPacketNumber = packetNumber;
		addPacket(data, 0, data.byteLength, headerBytes);
		if (!suspended) {
			setStatus(`Rx: ${packetNumber} · ${data.byteLength} bytes · avg ${latestAverageVoltage.toFixed(3)} V, ${latestAverageCurrent.toFixed(3)} A`);
		}
		updateStatus();
		requestRender(false);
	}

	function updateSampleInterval(packetNumber, sourceTimestampUs) {
		if (lastTimingPacketNumber !== null && lastSourceTimestampUs !== null) {
			const packetDelta = (packetNumber - lastTimingPacketNumber) >>> 0;
			const elapsedUs = (sourceTimestampUs - lastSourceTimestampUs) >>> 0;
			if (packetDelta > 0 && packetDelta <= 1000 && elapsedUs > 0 && elapsedUs < 0x80000000) {
				const measuredInterval = elapsedUs / (packetDelta * samplesPerPacket * 1000);
				if (measuredInterval >= 0.001 && measuredInterval <= 100) {
					timingIntervals.push(measuredInterval);
					if (timingIntervals.length > 32) timingIntervals.shift();
					timingSampleCount = timingIntervals.length;
					if (timingIntervals.length >= 32) {
						const sorted = timingIntervals.slice().sort((a, b) => a - b);
						const measuredMedian = (sorted[15] + sorted[16]) / 2;
						const deviations = sorted.map((value) => Math.abs(value - measuredMedian)).sort((a, b) => a - b);
						timingDeviationMs = (deviations[15] + deviations[16]) / 2;
						sampleIntervalMs += (measuredMedian - sampleIntervalMs) * 0.08;
						timingCalibrated = true;
					}
				}
			}
		}
		lastTimingPacketNumber = packetNumber;
		lastSourceTimestampUs = sourceTimestampUs;
	}

	function createSegment() {
		return new Int16Array(segmentSize * 2);
	}

	function getSummaryValue(list, index) {
		return list[Math.floor(index / summarySegmentSize)][index % summarySegmentSize];
	}

	function setSummaryValue(list, index, value) {
		const segmentIndex = Math.floor(index / summarySegmentSize);
		if (!list[segmentIndex]) list[segmentIndex] = new Int16Array(summarySegmentSize);
		list[segmentIndex][index % summarySegmentSize] = value;
	}

	function appendSample(rawVoltage, rawCurrent) {
		const segmentIndex = Math.floor(packetCount / segmentSize);
		if (!series.samples[segmentIndex]) series.samples[segmentIndex] = createSegment();
		const sampleOffset = (packetCount % segmentSize) * 2;
		series.samples[segmentIndex][sampleOffset] = rawVoltage;
		series.samples[segmentIndex][sampleOffset + 1] = rawCurrent;

		const summaryIndex = Math.floor(packetCount / samplesPerSummaryBlock);
		if (packetCount % samplesPerSummaryBlock === 0) {
			setSummaryValue(series.vMin, summaryIndex, rawVoltage);
			setSummaryValue(series.vMax, summaryIndex, rawVoltage);
			setSummaryValue(series.iMin, summaryIndex, rawCurrent);
			setSummaryValue(series.iMax, summaryIndex, rawCurrent);
		} else {
			setSummaryValue(series.vMin, summaryIndex, Math.min(getSummaryValue(series.vMin, summaryIndex), rawVoltage));
			setSummaryValue(series.vMax, summaryIndex, Math.max(getSummaryValue(series.vMax, summaryIndex), rawVoltage));
			setSummaryValue(series.iMin, summaryIndex, Math.min(getSummaryValue(series.iMin, summaryIndex), rawCurrent));
			setSummaryValue(series.iMax, summaryIndex, Math.max(getSummaryValue(series.iMax, summaryIndex), rawCurrent));
		}

		const coarseIndex = Math.floor(packetCount / samplesPerCoarseBlock);
		if (packetCount % samplesPerCoarseBlock === 0) {
			setSummaryValue(series.vCoarseMin, coarseIndex, rawVoltage);
			setSummaryValue(series.vCoarseMax, coarseIndex, rawVoltage);
			setSummaryValue(series.iCoarseMin, coarseIndex, rawCurrent);
			setSummaryValue(series.iCoarseMax, coarseIndex, rawCurrent);
		} else {
			setSummaryValue(series.vCoarseMin, coarseIndex, Math.min(getSummaryValue(series.vCoarseMin, coarseIndex), rawVoltage));
			setSummaryValue(series.vCoarseMax, coarseIndex, Math.max(getSummaryValue(series.vCoarseMax, coarseIndex), rawVoltage));
			setSummaryValue(series.iCoarseMin, coarseIndex, Math.min(getSummaryValue(series.iCoarseMin, coarseIndex), rawCurrent));
			setSummaryValue(series.iCoarseMax, coarseIndex, Math.max(getSummaryValue(series.iCoarseMax, coarseIndex), rawCurrent));
		}

		packetCount++;
	}

	function addPacket(data, offset, length, headerBytes = packetHeaderBytes, readoutTime = performance.now()) {
		const followLatest = chartMode === 'scope' || packetCount === 0 || viewEnd >= packetCount - 2;
		let samplesAdded = 0;
		let voltageSum = 0;
		let currentSum = 0;
		const end = offset + length;

		for (let position = offset + headerBytes; position + 3 < end; position += 4) {
			const rawVoltage = data.getInt16(position, false);
			const rawCurrent = data.getInt16(position + 2, false);
			appendSample(rawVoltage, rawCurrent);
			voltageSum += rawVoltage;
			currentSum += rawCurrent;
			samplesAdded++;
		}
		if (samplesAdded === 0) return;
		receivedPacketCount++;
		latestAverageVoltage = voltageSum / samplesAdded * busLsb;
		latestAverageCurrent = currentSum / samplesAdded * shuntLsb / shuntOhms;
		recentReadoutSamples.push({
			time: readoutTime,
			voltage: latestAverageVoltage,
			current: latestAverageCurrent,
			count: samplesAdded
		});

		if (followLatest) {
			if (chartMode === 'scope') {
				scrollToScopeWindow();
			} else {
				viewEnd = packetCount - 1;
			}
		}
	}

	function scrollToScopeWindow() {
		if (packetCount === 0) return;
		const visibleSamples = getScopeWindowSamples();
		viewEnd = packetCount - 1;
		viewStart = Math.max(0, packetCount - visibleSamples);
	}

	function getScopeWindowSamples() {
		return Math.max(1, Math.round((timePerDivisionSeconds * 10 * 1000) / sampleIntervalMs));
	}

	function getSample(index, channelIndex) {
		const segment = series.samples[Math.floor(index / segmentSize)];
		return segment[(index % segmentSize) * 2 + channelIndex];
	}

	function getMinMax(channelIndex, start, end) {
		let minimum = Infinity;
		let maximum = -Infinity;
		const minBlocks = channelIndex === 0 ? series.vMin : series.iMin;
		const maxBlocks = channelIndex === 0 ? series.vMax : series.iMax;
		const coarseMinBlocks = channelIndex === 0 ? series.vCoarseMin : series.iCoarseMin;
		const coarseMaxBlocks = channelIndex === 0 ? series.vCoarseMax : series.iCoarseMax;
		let index = Math.max(0, start);
		const limit = Math.min(packetCount, end);

		while (index < limit && index % samplesPerSummaryBlock !== 0) {
			const value = getSample(index, channelIndex);
			minimum = Math.min(minimum, value);
			maximum = Math.max(maximum, value);
			index++;
		}
		while (index + samplesPerSummaryBlock <= limit && index % samplesPerCoarseBlock !== 0) {
			const blockIndex = Math.floor(index / samplesPerSummaryBlock);
			minimum = Math.min(minimum, getSummaryValue(minBlocks, blockIndex));
			maximum = Math.max(maximum, getSummaryValue(maxBlocks, blockIndex));
			index += samplesPerSummaryBlock;
		}
		while (index + samplesPerCoarseBlock <= limit) {
			const blockIndex = Math.floor(index / samplesPerCoarseBlock);
			minimum = Math.min(minimum, getSummaryValue(coarseMinBlocks, blockIndex));
			maximum = Math.max(maximum, getSummaryValue(coarseMaxBlocks, blockIndex));
			index += samplesPerCoarseBlock;
		}
		while (index + samplesPerSummaryBlock <= limit) {
			const blockIndex = Math.floor(index / samplesPerSummaryBlock);
			minimum = Math.min(minimum, getSummaryValue(minBlocks, blockIndex));
			maximum = Math.max(maximum, getSummaryValue(maxBlocks, blockIndex));
			index += samplesPerSummaryBlock;
		}
		while (index < limit) {
			const value = getSample(index, channelIndex);
			minimum = Math.min(minimum, value);
			maximum = Math.max(maximum, value);
			index++;
		}
		return { minimum, maximum };
	}

	function saveRawBytes(dataView) {
		if (!db) return;
		let offset = 0;

		while (offset < dataView.byteLength) {
			if (writeIndex === bufferSize) switchAndFlushBuffer();
			const available = bufferSize - writeIndex;
			const count = Math.min(available, dataView.byteLength - offset);
			const source = new Uint8Array(dataView.buffer, dataView.byteOffset + offset, count);
			activeBuffer.set(source, writeIndex);
			writeIndex += count;
			offset += count;
		}
	}

	function saveFullBufferToDisk(bufferData, bytesCount) {
		if (!db || bytesCount === 0) return;
		const transaction = db.transaction(['chunks'], 'readwrite');
		transaction.objectStore('chunks').add(bufferData.slice(0, bytesCount));
		transaction.onerror = () => {
			console.error('Failed to persist BLE data:', transaction.error);
			setStatus('IndexedDB write failed; check available storage space');
		};
	}

	function switchAndFlushBuffer() {
		if (writeIndex === 0 || !db) return;
		const oldBuffer = activeBuffer;
		const oldLength = writeIndex;
		activeBuffer = standbyBuffer;
		standbyBuffer = oldBuffer;
		writeIndex = 0;
		saveFullBufferToDisk(oldBuffer, oldLength);
	}

	function updateStatus() {
		const elapsedMs = packetCount * sampleIntervalMs;
		const elapsed = formatDuration(elapsedMs);
		const bufferPercent = ((writeIndex / bufferSize) * 100).toFixed(1);
		const timing = timingCalibrated && timingDeviationMs / sampleIntervalMs < 0.25
			? 'measured step'
			: timingSampleCount > 0 ? 'variable step' : 'estimated step';
		statusOutput.textContent = `${elapsed} · ${formatBytes(totalBytes)} received · RAM buffer ${bufferPercent}% · ${packetCount.toLocaleString('en-US')} samples / ${receivedPacketCount.toLocaleString('en-US')} packets · ${timing} ${(sampleIntervalMs * 1000).toFixed(1)} us · ${wakeLockStatus}`;
	}

	function formatBytes(bytes) {
		if (bytes < 1024) return `${bytes} B`;
		if (bytes < 1024 * 1024) return `${(bytes / 1024).toFixed(1)} KB`;
		return `${(bytes / (1024 * 1024)).toFixed(2)} MB`;
	}

	function formatDuration(milliseconds) {
		const seconds = Math.floor(milliseconds / 1000);
		const hours = Math.floor(seconds / 3600);
		const minutes = Math.floor((seconds % 3600) / 60);
		return `${String(hours).padStart(2, '0')}:${String(minutes).padStart(2, '0')}:${String(seconds % 60).padStart(2, '0')}`;
	}

	function requestRender(force, updateNavigator = true) {
		if (updateNavigator) navigatorNeedsRender = true;
		if (suspended && !force) return;
		if (renderPending) return;
		renderPending = true;
		const render = () => {
			renderPending = false;
			if (suspended && !force) return;
			lastRender = performance.now();
			drawCharts(force);
			const expectedPacketIntervalMs = sampleIntervalMs * samplesPerPacket;
			if (chartMode === 'scope' && packetCount > 0 && lastPacketArrivalAt !== null &&
				performance.now() - lastPacketArrivalAt < Math.min(250, expectedPacketIntervalMs * 1.5)) {
				requestRender(false, false);
			}
		};
		if (chartMode === 'scope') {
			window.requestAnimationFrame(render);
		} else {
			const delay = force ? 0 : Math.max(0, 80 - (performance.now() - lastRender));
			window.setTimeout(render, delay);
		}
	}

	function resizeCanvas(canvas, context) {
		const rect = canvas.getBoundingClientRect();
		const ratio = Math.max(1, window.devicePixelRatio || 1);
		const width = Math.max(1, Math.round(rect.width * ratio));
		const height = Math.max(1, Math.round(rect.height * ratio));
		if (canvas.width !== width || canvas.height !== height) {
			canvas.width = width;
			canvas.height = height;
		}
		context.setTransform(ratio, 0, 0, ratio, 0, 0);
		return { width: rect.width, height: rect.height };
	}

	function drawCharts(force) {
		if (chartMode === 'scope' && lastPacketArrivalAt !== null && packetCount > 0) {
			const elapsedSincePacket = Math.max(0, performance.now() - lastPacketArrivalAt);
			const interpolatedSamples = Math.min(samplesPerPacket, elapsedSincePacket / sampleIntervalMs);
			viewEnd = packetCount - 1 + interpolatedSamples;
			viewStart = Math.max(0, viewEnd - getScopeWindowSamples() + 1);
		}
		const mainSize = resizeCanvas(mainCanvas, mainContext);
		drawMainChart(mainSize.width, mainSize.height);
		const now = performance.now();
		if (navigatorNeedsRender && (force || now - lastNavigatorRender >= 100)) {
			const navSize = resizeCanvas(navCanvas, navContext);
			drawNavigator(navSize.width, navSize.height);
			navigatorNeedsRender = false;
			lastNavigatorRender = now;
		}
		if (force || chartMode !== 'scope' || now - lastChartInfoUpdate >= 100) {
			updateChartInfo();
			lastChartInfoUpdate = now;
		}
	}

	function drawGrid(context, left, top, width, height, horizontalSteps = 8) {
		context.strokeStyle = '#242424';
		context.lineWidth = 1;
		context.setLineDash([]);
		context.beginPath();
		for (let step = 0; step <= horizontalSteps; step++) {
			const y = top + (height * step) / horizontalSteps;
			context.moveTo(left, y);
			context.lineTo(left + width, y);
		}
		for (let step = 0; step <= 10; step++) {
			const x = left + (width * step) / 10;
			context.moveTo(x, top);
			context.lineTo(x, top + height);
		}
		context.stroke();
	}

	function visibleSeries() {
		if (channel === 'V') return [{ index: 0, color: voltageColor, name: 'V', offset: vZeroOffset }];
		if (channel === 'I') return [{ index: 1, color: currentColor, name: 'I', offset: iZeroOffset }];
		return [
			{ index: 0, color: voltageColor, name: 'V', offset: vZeroOffset },
			{ index: 1, color: currentColor, name: 'I', offset: iZeroOffset }
		];
	}

	function drawMainChart(width, height) {
		const context = mainContext;
		context.clearRect(0, 0, width, height);
		const left = 48;
		const right = width - 48;
		const top = 24;
		const bottom = height - 22;
		const plotWidth = Math.max(1, right - left);
		const plotHeight = Math.max(1, bottom - top);
		drawGrid(context, left, top, plotWidth, plotHeight);

		if (packetCount === 0) {
			context.fillStyle = '#666';
			context.font = '14px sans-serif';
			context.textAlign = 'center';
			context.fillText('Waiting for data · use the navigator below to select a range', width / 2, height / 2);
			return;
		}

		const first = Math.max(0, Math.min(packetCount - 1, Math.floor(viewStart)));
		const last = Math.max(first, Math.min(packetCount - 1, Math.ceil(viewEnd)));
		const scopeWindow = chartMode === 'scope' ? getScopeWindowSamples() : last - first + 1;
		const axisLast = chartMode === 'scope' ? viewStart + scopeWindow - 1 : last;
		const visible = visibleSeries();
		const scales = visible.map((item) => {
			const range = getMinMax(item.index, first, last + 1);
			let minimum = range.minimum * (item.index === 0 ? busLsb : shuntLsb / shuntOhms);
			let maximum = range.maximum * (item.index === 0 ? busLsb : shuntLsb / shuntOhms);
			if (minimum === maximum) {
				const padding = Math.max(Math.abs(minimum) * 0.05, item.name === 'V' ? 0.1 : 0.01);
				minimum -= padding;
				maximum += padding;
			} else {
				const padding = (maximum - minimum) * 0.08;
				minimum -= padding;
				maximum += padding;
			}
			const midpoint = (minimum + maximum) / 2;
			const unitsPerDivision = item.index === 0 ? voltagePerDivision : currentPerDivision;
			const yZoom = item.index === 0 ? vYZoom : iYZoom;
			const halfRange = (unitsPerDivision * 8) / (2 * yZoom);
			minimum = midpoint - halfRange;
			maximum = midpoint + halfRange;
			return Object.assign({}, item, { minimum, maximum });
		});

		context.font = '11px Consolas, monospace';
		context.textAlign = 'right';
		for (let step = 0; step <= 4; step++) {
			const y = top + (plotHeight * step) / 4;
			const ratio = step / 4;
			const scale = scales[0];
			context.fillStyle = scale.color;
			const scaleValue = scale.maximum - (ratio - (scale.offset - 0.5)) * (scale.maximum - scale.minimum);
			context.fillText(scaleValue.toFixed(2), left - 5, y + 4);
			if (scales.length > 1) {
				context.textAlign = 'left';
				context.fillStyle = scales[1].color;
				const currentValue = scales[1].maximum -
					(ratio - (scales[1].offset - 0.5)) * (scales[1].maximum - scales[1].minimum);
				context.fillText(currentValue.toFixed(2), right + 5, y + 4);
				context.textAlign = 'right';
			}
		}

		scales.forEach((scale) => {
			const zeroY = valueToY(0, scale, top, plotHeight);
			if (zeroY >= top && zeroY <= bottom) {
				context.strokeStyle = `${scale.color}66`;
				context.setLineDash([5, 5]);
				context.beginPath();
				context.moveTo(left, zeroY);
				context.lineTo(right, zeroY);
				context.stroke();
			}
			drawEnvelope(context, scale, first, last, left, top, plotWidth, plotHeight);
			const handleY = Math.max(top + 7, Math.min(bottom - 7, zeroY));
			drawOffsetHandle(context, scale.name === 'V' ? left : right, handleY, scale.color, scale.name === 'V');
		});

		drawTimeAxis(context, left, right, bottom, first, axisLast);
		if (showCursors) {
			drawMeasurementCursors(context, left, top, plotWidth, plotHeight, first, axisLast, scales);
			drawCursorDelta(context, left, bottom, plotWidth, first, axisLast, height);
		}
	}

	function valueToY(value, scale, top, height) {
		const ratio = (scale.maximum - value) / (scale.maximum - scale.minimum);
		return top + ratio * height + (scale.offset - 0.5) * height;
	}

	function drawEnvelope(context, scale, first, last, left, top, width, height) {
		const pixels = Math.max(1, Math.floor(width));
		const visibleSamples = last - first + 1;
		const windowSamples = chartMode === 'scope' ? getScopeWindowSamples() : visibleSamples;
		const toPhysical = scale.index === 0 ? busLsb : shuntLsb / shuntOhms;
		context.setLineDash([]);

		if (visibleSamples <= pixels) {
			context.strokeStyle = scale.color;
			context.lineWidth = 1.8;
			context.beginPath();
			for (let index = first; index <= last; index++) {
				const xOffset = chartMode === 'scope'
						? (index - viewStart) / Math.max(1, windowSamples - 1)
					: (index - first) / Math.max(1, visibleSamples - 1);
				const x = left + xOffset * width;
				const y = valueToY(getSample(index, scale.index) * toPhysical, scale, top, height);
				if (index === first) context.moveTo(x, y);
				else context.lineTo(x, y);
			}
			if (chartMode === 'scope' && viewEnd > last) {
				const x = left + ((viewEnd - viewStart) / Math.max(1, windowSamples - 1)) * width;
				const y = valueToY(getSample(last, scale.index) * toPhysical, scale, top, height);
				context.lineTo(x, y);
			}
			context.stroke();
			return;
		}

		context.strokeStyle = `${scale.color}E6`;
		context.lineWidth = 1.6;
		context.beginPath();
		const columns = chartMode === 'scope' ? pixels : Math.min(pixels, visibleSamples);
		for (let pixel = 0; pixel < columns; pixel++) {
			const windowStart = chartMode === 'scope' ? viewStart : first;
			const start = Math.max(first, Math.ceil(windowStart + (windowSamples * pixel) / columns));
			const end = Math.min(last + 1, Math.ceil(windowStart + (windowSamples * (pixel + 1)) / columns));
			if (end <= start) continue;
			const range = getMinMax(scale.index, start, end);
			const x = left + ((pixel + 0.5) * width) / columns;
			context.moveTo(x, valueToY(range.minimum * toPhysical, scale, top, height));
			context.lineTo(x, valueToY(range.maximum * toPhysical, scale, top, height));
		}
		context.stroke();
	}

	function drawOffsetHandle(context, x, y, color, isLeft) {
		const direction = isLeft ? 1 : -1;
		context.fillStyle = color;
		context.beginPath();
		context.moveTo(x, y);
		context.lineTo(x + direction * 10, y - 6);
		context.lineTo(x + direction * 10, y + 6);
		context.closePath();
		context.fill();
	}

	function drawTimeAxis(context, left, right, bottom, first, last) {
		context.fillStyle = '#999';
		context.font = '10px Consolas, monospace';
		context.textAlign = 'center';
		for (let step = 0; step <= 4; step++) {
			const index = first + ((last - first) * step) / 4;
			const elapsed = Math.max(0, index * sampleIntervalMs);
			const x = left + ((right - left) * step) / 4;
			context.fillText(formatTimeDelta(elapsed), x, bottom + 15);
		}
	}

	function drawMeasurementCursors(context, left, top, width, height, first, last, scales) {
		const cursors = [
			{ position: cursorA, label: 'A', color: '#ff6262' },
			{ position: cursorB, label: 'B', color: '#ffe066' }
		];
		context.font = '11px Consolas, monospace';
		context.textAlign = 'left';
		for (const cursor of cursors) {
			const x = left + cursor.position * width;
			const index = Math.max(0, Math.min(packetCount - 1,
				Math.round(first + cursor.position * (last - first))
			));
			context.strokeStyle = cursor.color;
			context.setLineDash([4, 3]);
			context.beginPath();
			context.moveTo(x, top);
			context.lineTo(x, top + height);
			context.stroke();
			const values = scales.map((scale) => {
				const rawValue = getSample(index, scale.index);
				const value = rawValue * (scale.index === 0 ? busLsb : shuntLsb / shuntOhms);
				return `${scale.name} ${value.toFixed(3)}`;
			}).join(' ');
			context.fillStyle = cursor.color;
			context.fillText(`${cursor.label}: ${values}`, Math.min(x + 4, left + width - 100), top + 13);
		}
	}

	function drawCursorDelta(context, left, bottom, width, first, last, canvasHeight) {
		const indexA = first + cursorA * (last - first);
		const indexB = first + cursorB * (last - first);
		const deltaMs = (indexB - indexA) * sampleIntervalMs;
		const text = `Δt A→B: ${formatTimeDelta(deltaMs)}`;
		const centerX = left + ((cursorA + cursorB) / 2) * width;
		const y = Math.min(canvasHeight - 5, bottom - 7);
		context.font = '12px Consolas, monospace';
		context.fillStyle = '#ffe066';
		context.textAlign = 'center';
		context.fillText(text, centerX, y);
	}

	function formatTimeDelta(milliseconds) {
		const sign = milliseconds < 0 ? '−' : '';
		const absolute = Math.abs(milliseconds);
		if (absolute < 1) return `${sign}${(absolute * 1000).toFixed(0)} us`;
		if (absolute < 100) return `${sign}${absolute.toFixed(2)} ms`;
		if (absolute < 1000) return `${sign}${absolute.toFixed(1)} ms`;
		if (absolute < 60000) return `${sign}${(absolute / 1000).toFixed(2)} s`;
		return `${sign}${formatDuration(absolute)}`;
	}

	function drawNavigator(width, height) {
		const context = navContext;
		context.clearRect(0, 0, width, height);
		context.fillStyle = '#111';
		context.fillRect(0, 0, width, height);
		if (packetCount === 0) {
			context.fillStyle = '#555';
			context.font = '11px sans-serif';
			context.textAlign = 'center';
			context.fillText('Full recording overview', width / 2, height / 2 + 4);
			return;
		}

		const plottedSeries = visibleSeries();
		const overviewStart = chartMode === 'scope'
			? Math.max(0, packetCount - getScopeWindowSamples() * 10)
			: 0;
		const overviewCount = Math.max(1, packetCount - overviewStart);
		const plotWidth = Math.max(1, width - 2);
		for (const item of plottedSeries) {
			const fullRange = getMinMax(item.index, overviewStart, packetCount);
			let minimum = fullRange.minimum;
			let maximum = fullRange.maximum;
			if (minimum === maximum) {
				const padding = Math.max(1, Math.abs(minimum) * 0.05);
				minimum -= padding;
				maximum += padding;
			}
			const middle = height / 2;
			const amplitude = height * 0.38;
			context.strokeStyle = item.color;
			context.globalAlpha = 0.75;
			context.beginPath();
			for (let pixel = 0; pixel < plotWidth; pixel++) {
				const start = overviewStart + Math.floor((overviewCount * pixel) / plotWidth);
				const end = Math.min(packetCount, Math.max(start + 1,
					overviewStart + Math.floor((overviewCount * (pixel + 1)) / plotWidth)));
				const binRange = getMinMax(item.index, start, end);
				const yMin = middle - ((binRange.maximum - minimum) / (maximum - minimum)) * amplitude;
				const yMax = middle - ((binRange.minimum - minimum) / (maximum - minimum)) * amplitude;
				context.moveTo(pixel + 1, yMin);
				context.lineTo(pixel + 1, yMax);
			}
			context.stroke();
		}
		context.globalAlpha = 1;

		const startX = ((viewStart - overviewStart) / overviewCount) * width;
		const endX = ((viewEnd + 1 - overviewStart) / overviewCount) * width;
		context.fillStyle = 'rgba(120, 160, 220, 0.22)';
		context.fillRect(startX, 0, Math.max(3, endX - startX), height);
		context.strokeStyle = '#a8c6ff';
		context.lineWidth = 1;
		context.strokeRect(startX + 0.5, 0.5, Math.max(2, endX - startX - 1), height - 1);
	}

	function updateChartInfo() {
		if (packetCount === 0) {
			chartInfo.textContent = '';
			return;
		}
		const start = formatTimeDelta(viewStart * sampleIntervalMs);
		const end = formatTimeDelta(viewEnd * sampleIntervalMs);
		const modeInfo = chartMode === 'scope'
			? `Oscilloscope · ${formatTimeDelta(timePerDivisionSeconds * 1000)}/div · ${formatVoltageDivision(voltagePerDivision)}/div · ${formatCurrentDivision(currentPerDivision)}/div`
			: 'History';
		const timing = timingCalibrated && timingDeviationMs / sampleIntervalMs < 0.25
			? 'measured'
			: timingSampleCount > 0 ? 'variable' : 'estimated';
		chartInfo.textContent = `${modeInfo} · ${start}—${end} · ${timing} step ${(sampleIntervalMs * 1000).toFixed(1)} us`;
	}

	function formatVoltageDivision(value) {
		return value < 1 ? `${(value * 1000).toFixed(0)} mV` : `${value} V`;
	}

	function formatCurrentDivision(value) {
		return value < 1 ? `${(value * 1000).toFixed(0)} mA` : `${value} A`;
	}

	function plotBounds() {
		const rect = mainCanvas.getBoundingClientRect();
		return { left: 48, right: rect.width - 48, top: 24, bottom: rect.height - 22 };
	}

	function onMainPointerDown(event) {
		mainCanvas.setPointerCapture(event.pointerId);
		mainPointers.set(event.pointerId, { x: event.clientX, y: event.clientY });
		if (mainPointers.size === 2) {
			const [firstPointer, secondPointer] = Array.from(mainPointers.values());
			const bounds = plotBounds();
			const rect = mainCanvas.getBoundingClientRect();
			const initialRange = Math.max(1, viewEnd - viewStart);
			const anchorRatio = Math.max(0, Math.min(1,
				((firstPointer.x + secondPointer.x) / 2 - rect.left - bounds.left) /
				Math.max(1, bounds.right - bounds.left)
			));
			chartPinch = {
				startDistanceX: Math.max(24, Math.abs(secondPointer.x - firstPointer.x)),
				startDistanceY: Math.max(24, Math.abs(secondPointer.y - firstPointer.y)),
				vZoom: vYZoom,
				iZoom: iYZoom,
				start: viewStart,
				end: viewEnd,
				anchorRatio,
				anchorIndex: viewStart + anchorRatio * initialRange
			};
			mainDrag = null;
			return;
		}
		const rect = mainCanvas.getBoundingClientRect();
		const x = event.clientX - rect.left;
		const y = event.clientY - rect.top;
		const bounds = plotBounds();
		const cursorDistanceA = Math.abs(x - (bounds.left + cursorA * (bounds.right - bounds.left)));
		const cursorDistanceB = Math.abs(x - (bounds.left + cursorB * (bounds.right - bounds.left)));

		if (showCursors && Math.min(cursorDistanceA, cursorDistanceB) < 22) {
			mainDrag = { type: cursorDistanceA < cursorDistanceB ? 'cursorA' : 'cursorB' };
		} else if (Math.abs(x - bounds.left) < 20 && channel !== 'I') {
			mainDrag = { type: 'vOffset', y, value: vZeroOffset };
		} else if (Math.abs(x - bounds.right) < 20 && channel !== 'V') {
			mainDrag = { type: 'iOffset', y, value: iZeroOffset };
		} else {
			mainDrag = { type: 'pan', x, start: viewStart, end: viewEnd };
		}
	}

	function onMainPointerMove(event) {
		if (mainPointers.has(event.pointerId)) {
			mainPointers.set(event.pointerId, { x: event.clientX, y: event.clientY });
		}
		if (chartPinch && mainPointers.size >= 2) {
			const [firstPointer, secondPointer] = Array.from(mainPointers.values());
			const distanceX = Math.max(24, Math.abs(secondPointer.x - firstPointer.x));
			const distanceY = Math.max(24, Math.abs(secondPointer.y - firstPointer.y));
			const zoomRatioX = distanceX / chartPinch.startDistanceX;
			const zoomRatioY = distanceY / chartPinch.startDistanceY;
			if (channel !== 'I') vYZoom = Math.max(0.1, Math.min(100, chartPinch.vZoom * zoomRatioY));
			if (channel !== 'V') iYZoom = Math.max(0.1, Math.min(100, chartPinch.iZoom * zoomRatioY));

			const initialRange = Math.max(1, chartPinch.end - chartPinch.start);
			const nextRange = Math.max(1, Math.min(packetCount - 1, initialRange / zoomRatioX));
			const nextStart = chartPinch.anchorIndex - chartPinch.anchorRatio * nextRange;
			setViewRange(nextStart, nextStart + nextRange);
			requestRender(true);
			return;
		}
		if (!mainDrag || packetCount < 2) return;
		const rect = mainCanvas.getBoundingClientRect();
		const x = event.clientX - rect.left;
		const y = event.clientY - rect.top;
		const bounds = plotBounds();
		const plotWidth = Math.max(1, bounds.right - bounds.left);
		const visibleCount = Math.max(1, viewEnd - viewStart);

		if (mainDrag.type === 'cursorA' || mainDrag.type === 'cursorB') {
			const value = Math.max(0, Math.min(1, (x - bounds.left) / plotWidth));
			if (mainDrag.type === 'cursorA') cursorA = value;
			else cursorB = value;
		} else if (mainDrag.type === 'vOffset' || mainDrag.type === 'iOffset') {
			const value = Math.max(-4, Math.min(4,
				mainDrag.value + (y - mainDrag.y) / Math.max(1, bounds.bottom - bounds.top)));
			if (mainDrag.type === 'vOffset') vZeroOffset = value;
			else iZeroOffset = value;
		} else {
			const shift = ((x - mainDrag.x) / plotWidth) * visibleCount;
			const range = mainDrag.end - mainDrag.start;
			const start = Math.max(0, Math.min(packetCount - 1 - range, mainDrag.start - shift));
			setViewRange(start, start + range);
		}
		requestRender(true);
	}

	function onMainPointerUp(event) {
		mainPointers.delete(event.pointerId);
		if (mainPointers.size < 2) chartPinch = null;
		mainDrag = null;
		saveSettings();
	}

	function onMainWheel(event) {
		event.preventDefault();
		if (packetCount < 2) return;
		const rect = mainCanvas.getBoundingClientRect();
		const bounds = plotBounds();
		const anchor = Math.max(0, Math.min(1, (event.clientX - rect.left - bounds.left) / (bounds.right - bounds.left)));
		const currentLength = Math.max(1, viewEnd - viewStart);
		const nextLength = Math.max(1, Math.min(packetCount - 1, currentLength * (event.deltaY < 0 ? 0.8 : 1.25)));
		const position = viewStart + anchor * currentLength;
		setViewRange(position - anchor * nextLength, position + (1 - anchor) * nextLength);
		requestRender(true);
	}

	function onNavPointerDown(event) {
		if (chartMode === 'scope') return;
		navCanvas.setPointerCapture(event.pointerId);
		const rect = navCanvas.getBoundingClientRect();
		const x = Math.max(0, Math.min(1, (event.clientX - rect.left) / rect.width));
		const start = viewStart / Math.max(1, packetCount - 1);
		const end = viewEnd / Math.max(1, packetCount - 1);
		const nearStart = Math.abs(x - start) < 0.04;
		const nearEnd = Math.abs(x - end) < 0.04;
		if (nearStart) navDrag = { type: 'start' };
		else if (nearEnd) navDrag = { type: 'end' };
		else if (x > start && x < end && (start > 0.02 || end < 0.98)) navDrag = { type: 'move', pointer: x, start, end };
		else navDrag = { type: 'new', start: x };
		if (navDrag.type === 'new') setViewRange(x * (packetCount - 1), x * (packetCount - 1));
		requestRender(true);
	}

	function onNavPointerMove(event) {
		if (!navDrag || packetCount < 2) return;
		const rect = navCanvas.getBoundingClientRect();
		const position = Math.max(0, Math.min(1, (event.clientX - rect.left) / rect.width));
		if (navDrag.type === 'new') {
			setViewRange(navDrag.start * (packetCount - 1), position * (packetCount - 1));
		} else if (navDrag.type === 'start') {
			setViewRange(position * (packetCount - 1), viewEnd);
		} else if (navDrag.type === 'end') {
			setViewRange(viewStart, position * (packetCount - 1));
		} else {
			const shift = position - navDrag.pointer;
			const range = navDrag.end - navDrag.start;
			const start = Math.max(0, Math.min(1 - range, navDrag.start + shift));
			setViewRange(start * (packetCount - 1), (start + range) * (packetCount - 1));
		}
		requestRender(true);
	}

	function onNavPointerUp() {
		navDrag = null;
	}

	function setViewRange(start, end) {
		if (packetCount < 2) {
			viewStart = 0;
			viewEnd = Math.max(0, packetCount - 1);
			return;
		}
		let left = Math.max(0, Math.min(packetCount - 1, start));
		let right = Math.max(0, Math.min(packetCount - 1, end));
		if (left > right) [left, right] = [right, left];
		if (chartMode === 'scope') {
			left = Math.round(left);
			right = Math.round(right);
		}
		if (right - left < 1) right = Math.min(packetCount - 1, left + 1);
		viewStart = left;
		viewEnd = right;
	}

	function toggleCursors() {
		showCursors = !showCursors;
		const button = document.getElementById('cursor-btn');
		button.textContent = `Cursors: ${showCursors ? 'On' : 'Off'}`;
		button.setAttribute('aria-pressed', String(showCursors));
		saveSettings();
		requestRender(true);
	}

	function clearRecording() {
		if (!window.confirm('Delete the saved recording and clear the charts?')) return;
		if (!db) {
			setStatus('Storage is not ready yet');
			return;
		}
		const transaction = db.transaction(['chunks'], 'readwrite');
		transaction.objectStore('chunks').clear();
		transaction.oncomplete = () => {
			resetHistory();
			setStatus('Recording cleared');
		};
		transaction.onerror = () => {
			console.error('Failed to clear IndexedDB:', transaction.error);
			setStatus('Failed to clear IndexedDB');
		};
	}

	function resetHistory() {
		for (const key of Object.keys(series)) series[key] = [];
		packetCount = 0;
		receivedPacketCount = 0;
		totalBytes = 0;
		latestAverageVoltage = null;
		latestAverageCurrent = null;
		recentReadoutSamples.length = 0;
		updateReadout();
		firstPacketNumber = null;
		lastTimingPacketNumber = null;
		lastSourceTimestampUs = null;
		timingIntervals.length = 0;
		timingSampleCount = 0;
		timingDeviationMs = 0;
		timingCalibrated = false;
		sampleIntervalMs = nominalPacketIntervalMs / samplesPerPacket;
		recordStartTime = 0;
		viewStartTime = 0;
		viewStart = 0;
		viewEnd = 0;
		writeIndex = 0;
		activeBuffer.fill(0);
		standbyBuffer.fill(0);
		vZeroOffset = 0.5;
		iZeroOffset = 0.5;
		vYZoom = 1;
		iYZoom = 1;
		updateStatus();
		saveSettings();
		requestRender(true);
	}

	downloadDailyLog = function() {
		if (!db) {
			setStatus('Storage is not ready yet');
			return;
		}
		const transaction = db.transaction(['chunks'], 'readonly');
		const request = transaction.objectStore('chunks').getAll();
		request.onsuccess = () => {
			const chunks = request.result;
			const parts = chunks.slice();
			if (writeIndex > 0) parts.push(activeBuffer.slice(0, writeIndex));
			if (parts.length === 0) {
				setStatus('No data to download');
				return;
			}
			const header = new ArrayBuffer(8);
			new DataView(header).setBigUint64(0, BigInt(recordStartTime || Date.now()), false);
			parts.unshift(header);
			const blob = new Blob(parts, { type: 'application/octet-stream' });
			const url = URL.createObjectURL(blob);
			const link = document.createElement('a');
			link.href = url;
			link.download = `ble_log_${new Date(recordStartTime || Date.now()).toISOString().slice(0, 10)}_${Date.now()}.bin`;
			document.body.appendChild(link);
			link.click();
			link.remove();
			window.setTimeout(() => URL.revokeObjectURL(url), 30000);
			setStatus(`File downloaded: ${formatBytes(blob.size)}`);

			window.setTimeout(() => {
				const clearTransaction = db.transaction(['chunks'], 'readwrite');
				clearTransaction.objectStore('chunks').clear();
				clearTransaction.oncomplete = () => {
					recordStartTime = 0;
					writeIndex = 0;
					activeBuffer.fill(0);
					standbyBuffer.fill(0);
				};
				clearTransaction.onerror = () => {
					console.error('Failed to clear downloaded data:', clearTransaction.error);
					setStatus('File downloaded, but IndexedDB could not be cleared');
				};
			}, 1000);
		};
		request.onerror = () => {
			console.error('Failed to read recording from IndexedDB:', request.error);
			setStatus('Failed to read recording from IndexedDB');
		};
	};

	uploadDailyLog = function() {
		const input = document.createElement('input');
		input.type = 'file';
		input.accept = '.bin,application/octet-stream';
		input.addEventListener('change', async () => {
			const file = input.files && input.files[0];
			if (!file) return;
			if (file.size < 8) {
				setStatus('File is too short or corrupted');
				return;
			}
			try {
				await importRecording(file);
			} catch (error) {
				console.error('Failed to open recording:', error);
				setStatus(`Could not open file: ${error.message}`);
			}
		}, { once: true });
		input.click();
	};

	async function importRecording(file) {
		const headerBuffer = await file.slice(0, 8).arrayBuffer();
		const startTimestamp = Number(new DataView(headerBuffer).getBigUint64(0, false));
		const dataLength = file.size - 8;
		const filePacketBytes = dataLength % packetBytes === 0
			? packetBytes
			: dataLength % legacyPacketBytes === 0 ? legacyPacketBytes : 0;
		const fileHeaderBytes = filePacketBytes === packetBytes
			? packetHeaderBytes
			: filePacketBytes === legacyPacketBytes ? legacyPacketHeaderBytes : 0;
		if (filePacketBytes === 0) {
			setStatus('File does not contain complete 408-byte or legacy 404-byte packets');
			return;
		}
		const fullPackets = Math.floor(dataLength / filePacketBytes);
		if (fullPackets === 0) {
			setStatus('No complete packets were found in the file');
			return;
		}
		resetHistory();
		sampleIntervalMs = nominalPacketIntervalMs / samplesPerPacket;
		timingSampleCount = 0;
		timingDeviationMs = 0;
		lastTimingPacketNumber = null;
		recordStartTime = startTimestamp;
		viewStartTime = startTimestamp;
		totalBytes = file.size - 8;
		setStatus(`Opening ${file.name}: ${fullPackets.toLocaleString('en-US')} packets…`);

		const packetsPerBatch = 2048;
		for (let packet = 0; packet < fullPackets; packet += packetsPerBatch) {
			const batchCount = Math.min(packetsPerBatch, fullPackets - packet);
			const start = 8 + packet * filePacketBytes;
			const buffer = await file.slice(start, start + batchCount * filePacketBytes).arrayBuffer();
			const view = new DataView(buffer);
			for (let index = 0; index < batchCount; index++) {
				const offset = index * filePacketBytes;
				if (packet === 0 && index === 0) firstPacketNumber = view.getUint32(offset, false);
				if (fileHeaderBytes === packetHeaderBytes) {
					updateSampleInterval(view.getUint32(offset, false), view.getUint32(offset + 4, false));
				}
				const importedPacketIndex = packet + index;
				const readoutTime = performance.now() -
					((fullPackets - importedPacketIndex - 1) * nominalPacketIntervalMs);
				addPacket(view, offset, filePacketBytes, fileHeaderBytes, readoutTime);
			}
			setStatus(`Opening ${file.name}: ${Math.min(fullPackets, packet + batchCount).toLocaleString('en-US')} / ${fullPackets.toLocaleString('en-US')} packets`);
			requestRender(true);
			await new Promise((resolve) => window.setTimeout(resolve, 0));
		}
		if (chartMode === 'scope') {
			scrollToScopeWindow();
		} else {
			viewStart = 0;
			viewEnd = Math.max(0, packetCount - 1);
		}
		updateStatus();
		setStatus(`Opened ${file.name} · ${formatBytes(file.size)}`);
		requestRender(true);
	}

	initPage();
})();
