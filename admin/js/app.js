// Global State
let currentConfig = {};
let originalConfig = {};
let modifiedSections = new Set();

// Initialize Theme
function initializeTheme() {
    const saved = localStorage.getItem('theme');
    let theme = saved;
    
    if (!saved) {
        theme = window.matchMedia('(prefers-color-scheme: dark)').matches ? 'dark' : 'light';
    }
    
    applyTheme(theme);
}

function applyTheme(theme) {
    if (theme === 'dark') {
        document.documentElement.classList.add('dark-mode');
        localStorage.setItem('theme', 'dark');
    } else {
        document.documentElement.classList.remove('dark-mode');
        localStorage.setItem('theme', 'light');
    }
}

function toggleTheme() {
    const isDark = document.documentElement.classList.contains('dark-mode');
    applyTheme(isDark ? 'light' : 'dark');
}

// Toast Notifications
function showToast(message, type = 'info') {
    const toast = document.createElement('div');
    toast.className = `toast toast-${type}`;
    toast.textContent = message;
    document.body.appendChild(toast);
    
    setTimeout(() => toast.classList.add('show'), 10);
    
    setTimeout(() => {
        toast.classList.remove('show');
        setTimeout(() => toast.remove(), 300);
    }, 3000);
}

// Load Configuration
async function loadConfig() {
    try {
        const response = await fetch('/admin/config.json?_t=' + Date.now(), {
            headers: {
                'Cache-Control': 'no-cache, no-store, must-revalidate',
                'Pragma': 'no-cache',
                'Expires': '0'
            }
        });
        
        if (!response.ok) throw new Error('خطا در بارگذاری پیکربندی');
        
        currentConfig = await response.json();
        originalConfig = JSON.parse(JSON.stringify(currentConfig));
        
        return currentConfig;
    } catch (error) {
        showToast('خطا در بارگذاری پیکربندی: ' + error.message, 'error');
        return null;
    }
}

// Save Configuration
async function saveConfig(data) {
    try {
        const response = await fetch('/admin/config.json', {
            method: 'PUT',
            headers: {
                'Content-Type': 'application/json'
            },
            body: JSON.stringify(data)
        });
        
        if (!response.ok) throw new Error('خطا در ذخیره پیکربندی');
        
        showToast('پیکربندی با موفقیت ذخیره شد', 'success');
        return true;
    } catch (error) {
        showToast('خطا در ذخیره پیکربندی: ' + error.message, 'error');
        return false;
    }
}

// Copy to Clipboard
function copyToClipboard(text) {
    navigator.clipboard.writeText(text).then(() => {
        showToast('کپی شد!', 'success');
    }).catch(() => {
        showToast('خطا در کопи کردن', 'error');
    });
}

// Module Toggle
function toggleModule(titleEl) {
    const module = titleEl.closest('.module');
    module.classList.toggle('collapsed');
}

// Mark Section as Modified
function markModified(section) {
    modifiedSections.add(section);
    updateButtonStates();
}

function updateButtonStates() {
    const sections = ['sub', 'config', 'ech', 'proxy', 'convert', 'notification'];
    
    sections.forEach(section => {
        const saveBtn = document.getElementById(`save${section.charAt(0).toUpperCase() + section.slice(1)}Btn`);
        const cancelBtn = document.getElementById(`cancel${section.charAt(0).toUpperCase() + section.slice(1)}Btn`);
        
        if (saveBtn && cancelBtn) {
            const isModified = modifiedSections.has(section);
            saveBtn.disabled = !isModified;
            cancelBtn.disabled = !isModified;
        }
    });
}

// Reset Section
function resetSection(section) {
    if (section === 'sub') {
        loadSubscriptionConfig();
    } else if (section === 'config') {
        loadConfigDetails();
    } else if (section === 'ech') {
        loadECHConfig();
    } else if (section === 'proxy') {
        loadProxyConfig();
    } else if (section === 'convert') {
        loadConvertConfig();
    } else if (section === 'notification') {
        loadNotificationConfig();
    }
    
    modifiedSections.delete(section);
    updateButtonStates();
}

// QR Code Modal
function showQRCode(elementId) {
    const input = document.getElementById(elementId);
    if (!input || !input.value) {
        showToast('لینکی موجود نیست', 'error');
        return;
    }
    
    const modal = document.getElementById('qrcodeModal');
    const container = document.getElementById('qrcodeContainer');
    
    container.innerHTML = '';
    
    if (typeof QRCode !== 'undefined') {
        new QRCode(container, {
            text: input.value,
            width: 200,
            height: 200,
            colorDark: '#000000',
            colorLight: '#808080',
            correctLevel: QRCode.CorrectLevel.M
        });
    }
    
    modal.classList.add('show');
}

function closeQRCode(event) {
    if (event && event.target !== event.currentTarget) return;
    const modal = document.getElementById('qrcodeModal');
    if (modal) modal.classList.remove('show');
}

// Subscription Links
function copySubscription(elementId) {
    const input = document.getElementById(elementId);
    if (input && input.value) {
        copyToClipboard(input.value);
    }
}

// Generate Subscription Links
function generateSubscriptionLinks() {
    const token = currentConfig.优选订阅生成?.TOKEN;
    const host = window.location.host;
    
    return {
        link: currentConfig.LINK,
        sub: `https://${host}/sub?token=${token}`,
        base64: `https://${host}/sub?token=${token}&b64`,
        clash: `https://${host}/sub?token=${token}&clash`,
        singbox: `https://${host}/sub?token=${token}&sb`
    };
}

// Logout
function logout() {
    if (confirm('آیا می‌خواهید از پنل خارج شوید؟')) {
        window.location.href = '/admin/login.html';
    }
}

// Reset Config
function resetConfigWithConfirm() {
    const modal = document.getElementById('resetModal');
    if (modal) modal.classList.add('show');
}

function closeResetModal(event) {
    if (event && event.target !== event.currentTarget) return;
    const modal = document.getElementById('resetModal');
    if (modal) modal.classList.remove('show');
}

async function confirmReset() {
    try {
        const response = await fetch('/admin/config.json', {
            method: 'DELETE'
        });
        
        if (response.ok) {
            showToast('تنظیمات با موفقیت بازنشانی شد', 'success');
            location.reload();
        } else {
            throw new Error('خطا در بازنشانی');
        }
    } catch (error) {
        showToast('خطا: ' + error.message, 'error');
    }
    
    closeResetModal();
}

// Mobile Menu
function toggleSidebar() {
    const sidebar = document.querySelector('.sidebar');
    if (sidebar) {
        sidebar.classList.toggle('open');
    }
}

// Close sidebar when clicking outside on mobile
document.addEventListener('click', function(event) {
    const sidebar = document.querySelector('.sidebar');
    const menuToggle = document.querySelector('.menu-toggle');
    
    if (sidebar && menuToggle) {
        if (!sidebar.contains(event.target) && !menuToggle.contains(event.target)) {
            sidebar.classList.remove('open');
        }
    }
});

// Initialize on page load
document.addEventListener('DOMContentLoaded', function() {
    initializeTheme();
});

// Latency Test Configuration
const latencyTestConfig = {
    count: 16
};

// Latency Sites Data
const latencySites = [
    { name: 'Douyin', region: 'داخلی', icon: '🎵', url: 'https://lf3-zlink-tos.ugurl.cn/obj/zebra-public/resource_lmmizj_1632398893.png' },
    { name: 'Bilibili', region: 'داخلی', icon: '📺', url: 'https://i0.hdslb.com/bfs/face/member/noface.jpg@24w_24h_1c' },
    { name: 'GitHub', region: 'بین‌المللی', icon: '🐙', url: 'https://github.github.io/janky/images/bg_hr.png' },
    { name: 'Telegram', region: 'بین‌المللی', icon: '✈️', url: 'https://web.telegram.org/k/' },
    { name: 'X.com', region: 'بین‌المللی', icon: '🐦', url: 'https://abs.twimg.com/favicons/twitter.3.ico' },
    { name: 'YouTube', region: 'بین‌المللی', icon: '▶️', url: 'https://www.youtube.com/favicon.ico' }
];

// Test Latency
async function testLatency(site) {
    const start = Date.now();
    try {
        await fetch(site.url + '?t=' + Date.now(), {
            method: 'HEAD',
            cache: 'no-cache',
            mode: 'no-cors'
        });
        return Date.now() - start;
    } catch (error) {
        return -1;
    }
}

// Get Latency Color
function getLatencyColor(latency) {
    if (latency === -1) return '#ef4444';
    if (latency <= 49) return '#10b981';
    if (latency <= 149) return '#83DA00';
    if (latency <= 299) return '#f59e0b';
    if (latency <= 999) return '#ff404a';
    return '#c40003';
}

// Network Info
async function loadNetworkInfo() {
    const endpoints = [
        { id: 'ipip', url: 'https://ip.sb/ip', name: 'تست داخلی' },
        { id: 'overseas', url: 'https://api.ip.sb/ip', name: 'تست خارجی' },
        { id: 'cf', url: 'https://cloudflare.com/cdn-cgi/trace', name: 'CloudFlare' },
        { id: 'twitter', url: 'https://x.com/', name: 'تست فیلترشکن' }
    ];
    
    for (const endpoint of endpoints) {
        const statusEl = document.getElementById(`status-${endpoint.id}`);
        const ipEl = document.getElementById(`${endpoint.id}-ip`);
        const countryEl = document.getElementById(`${endpoint.id}-country`);
        
        if (statusEl) statusEl.className = 'status-indicator loading';
        
        try {
            const response = await fetch(endpoint.url, { mode: 'cors' });
            let ip = '';
            
            if (endpoint.id === 'cf') {
                const text = await response.text();
                const match = text.match(/ip=(\d+\.\d+\.\d+\.\d+)/);
                ip = match ? match[1] : '';
            } else {
                ip = await response.text();
            }
            
            ip = ip.trim();
            
            if (ipEl) ipEl.textContent = ip || '-';
            if (statusEl) statusEl.className = 'status-indicator success';
            
            // Get country info
            if (ip && countryEl) {
                try {
                    const geoResponse = await fetch(`https://ipapi.co/${ip}/json/`);
                    const geoData = await geoResponse.json();
                    countryEl.textContent = geoData.country_name || '-';
                } catch {
                    countryEl.textContent = '-';
                }
            }
        } catch (error) {
            if (ipEl) ipEl.textContent = 'خطا';
            if (statusEl) statusEl.className = 'status-indicator error';
        }
    }
}

// CF Usage Display
function updateCFUsageDisplay(cfUsage) {
    const workers = cfUsage.workers || 0;
    const pages = cfUsage.pages || 0;
    const total = cfUsage.total || 0;
    const dailyQuota = cfUsage.max || 100000;
    
    document.getElementById('cfWorkerCount').textContent = workers.toLocaleString();
    document.getElementById('cfPagesCount').textContent = pages.toLocaleString();
    document.getElementById('cfDailyQuota').textContent = dailyQuota.toLocaleString();
    document.getElementById('cfTotalDisplay').textContent = total.toLocaleString();
    
    const percentage = ((total / dailyQuota) * 100).toFixed(2);
    const workersRatio = (workers / dailyQuota) * 100;
    const pagesRatio = (pages / dailyQuota) * 100;
    
    const workerBarEl = document.getElementById('cfWorkerBar');
    if (workerBarEl) workerBarEl.style.width = Math.min(workersRatio, 100) + '%';
    
    const pagesBarEl = document.getElementById('cfPagesBar');
    if (pagesBarEl) {
        pagesBarEl.style.width = Math.min(pagesRatio, 100 - workersRatio) + '%';
        pagesBarEl.style.left = Math.min(workersRatio, 100) + '%';
    }
    
    const percentageCenterEl = document.getElementById('cfPercentageCenter');
    if (percentageCenterEl) {
        percentageCenterEl.textContent = `میزان استفاده: ${total.toLocaleString()} (${percentage}%)`;
    }
}

// Line Editor
function initLineEditor(textareaId) {
    const ta = document.getElementById(textareaId);
    if (!ta) return;
    
    function render() {
        if (ta._refreshLineEditor) {
            ta._refreshLineEditor();
        }
    }
    
    ta.addEventListener('input', render);
    ta.addEventListener('scroll', () => {
        const mirror = ta.closest('.line-editor')?.querySelector('.mirror');
        if (mirror) mirror.scrollTop = ta.scrollTop;
    });
    
    render();
}

// API Functions for Optimization
async function startOptimize() {
    const progressBar = document.getElementById('optimizeProgressBar');
    const progressFill = document.getElementById('optimizeProgressFill');
    const progressText = document.getElementById('optimizeProgressText');
    const resultsTabs = document.getElementById('optimizeResultsTabs');
    const resultsContent = document.getElementById('optimizeResultsContent');
    
    if (progressBar) progressBar.classList.remove('hidden-section');
    
    const ipLibrary = document.getElementById('optimizeIPLibrary')?.value || 'cf-official';
    const port = document.getElementById('optimizePort')?.value || '443';
    const concurrency = parseInt(document.getElementById('optimizeConcurrency')?.value) || 8;
    
    // Simulate optimization progress
    for (let i = 0; i <= 100; i += 10) {
        if (progressFill) progressFill.style.width = i + '%';
        if (progressText) progressText.textContent = `${i}/512 (${i.toFixed(2)}%)`;
        await new Promise(resolve => setTimeout(resolve, 500));
    }
    
    if (resultsTabs) resultsTabs.classList.remove('hidden-section');
    if (resultsContent) {
        resultsContent.classList.remove('hidden-section');
        resultsContent.innerHTML = '<p>نتایج بهینه‌سازی...</p>';
    }
    
    document.getElementById('btnSaveOverride')?.removeAttribute('disabled');
    document.getElementById('btnSaveAppend')?.removeAttribute('disabled');
}

// Helper Functions
function normalizePath(path) {
    if (!path) return path;
    let normalized = path.split('#')[0].trim();
    if (normalized && !normalized.startsWith('/')) {
        normalized = '/' + normalized;
    }
    return normalized;
}

function extractDomain(url) {
    try {
        url = url.trim();
        if (!url.includes('://')) {
            if (url.includes('/') || url.includes('?') || url.includes(':')) {
                url = 'https://' + url;
            } else {
                return url;
            }
        }
        const urlObj = new URL(url);
        let domain = urlObj.hostname;
        if (domain.startsWith('www.')) {
            domain = domain.substring(4);
        }
        return domain;
    } catch {
        let temp = url.trim();
        if (temp.includes('://')) temp = temp.split('://')[1];
        if (temp.includes('/')) temp = temp.split('/')[0];
        if (temp.includes('?')) temp = temp.split('?')[0];
        if (temp.includes(':')) temp = temp.split(':')[0];
        if (temp.startsWith('www.')) temp = temp.substring(4);
        return temp;
    }
}

// Export functions for use in pages
window.AdminPanel = {
    loadConfig,
    saveConfig,
    copyToClipboard,
    showToast,
    applyTheme,
    toggleTheme,
    markModified,
    resetSection,
    showQRCode,
    closeQRCode,
    copySubscription,
    generateSubscriptionLinks,
    logout,
    resetConfigWithConfirm,
    closeResetModal,
    confirmReset,
    toggleSidebar,
    testLatency,
    getLatencyColor,
    loadNetworkInfo,
    updateCFUsageDisplay,
    initLineEditor,
    startOptimize,
    normalizePath,
    extractDomain,
    currentConfig: () => currentConfig
};
