# پنل Nova Proxy

> ⚡ پنل مدیریت VLESS برای Cloudflare Workers

<p align="center">
  <img src="https://img.shields.io/badge/Cloudflare-Workers-F38020?style=for-the-badge&logo=cloudflare" alt="Cloudflare Workers">
  <img src="https://img.shields.io/badge/VLESS-Protocol-blue?style=for-the-badge">
  <img src="https://img.shields.io/badge/TLS-ECH-green?style=for-the-badge">
</p>

---

## ✨ امکانات

### 🔐 پروتکل‌های پشتیبانی شده
- **VLESS** - پروتکل اصلی
- **Trojan** - پروتکل جایگزین

### 🌐 انواع اتصال
- **WebSocket** - استاندارد
- **HTTP/2** - سریع‌تر
- **HTTP/3 (gRPC)** - مدرن‌ترین

### 🔒 امنیت
- **TLS** - رمزنگاری
- **ECH** (Encrypted Client Hello) - پنهان‌سازی SNI
- **0-RTT** - اتصال سریع‌تر
- **تأیید证书** - قابل تنظیم

### 📡 سیستم اشتراک
- اشتراک محلی با IP های تصادفی Cloudflare
- پشتیبانی از API های خارجی (SUB Generator)
- تبدیل خودکار به فرمت‌های مختلف
- پشتیبانی از: Clash, Sing-box, Surge, Quantumult, Loon

### 🖥️ پنل مدیریت
- تنظیمات کامل از طریق وب
- بهینه‌سازی آنلاین IP
- نمایش آمار استفاده Cloudflare
- تنظیمات سفارشی IP

### 📱 امکانات اضافی
- **تلگرام** - اعلان‌ها و مدیریت
- **SOCKS5/HTTP Proxy** - پروکسی سفارشی
- **Anti-Proxy Fallback** - مکانیزم بازگشت

---

## 📋 متغیرهای محیطی (Environment Variables)

برای استقرار این پروژه، متغیرهای زیر را در Cloudflare Workers تنظیم کنید:

| متغیر | الزامی | توضیحات | مثال |
|--------|---------|----------|-------|
| `ADMIN` | ✅ | رمز عبور مدیر | `MySecurePassword123` |
| `KEY` | ✅ | کلید رمزنگاری | `YourSecretKey` |
| `UUID` | ❌ | UUID سفارشی (اختیاری) | `550e8400-e29b-41d4-a716-446655440000` |
| `HOST` | ❌ | دامنه هاست | `example.com` |
| `KV` | ❌ | Namespace برای KV | `nova-kv` |
| `PROXYIP` | ❌ | IP پروکسی | `proxy.example.com` |
| `GO2SOCKS5` | ❌ | لیست SOCKS5 | `socks5://user:pass@host:port` |
| `URL` | ❌ | صفحه فریب (Fake) | `nginx` یا دامنه |
| `ECH` | ❌ | فعال‌سازی ECH | `true` |

---

## 🚀 نحوه استقرار

### ۱. ایجاد Worker
1. به داشبورد Cloudflare بروید
2. یک Worker جدید ایجاد کنید
3. کد `nvless.js` را کپی کنید

### ۲. تنظیم متغیرها
در بخش Settings > Environment Variables:

```
ADMIN = رمز_عبور_شما
KEY = کلید_امنیتی
UUID = (اختیاری) UUID دلخواه
KV = namespace-name
HOST = دامنه_شما
```

### ۳. ایجاد KV Namespace
1. به Cloudflare Workers > KV بروید
2. یک Namespace جدید ایجاد کنید
3. نام آن را در متغیر `KV` وارد کنید

### ۴. اتصال Domain
1. یک Subdomain به Worker متصل کنید
2. یا از Routes استفاده کنید

---

## 📖 راهنمای استفاده

### 🔗 دریافت اشتراک

```
https://your-domain/sub?token=TOKEN
```

پارامترهای اضافی:
- `&target=clash` - فرمت Clash
- `&target=singbox` - فرمت Sing-box
- `&target=surge` - فرمت Surge
- `&target=mixed` - ترکیبی (پیش‌فرض)
- `&base64=true` - خروجی Base64
- `&sub=URL` - استفاده از API خارجی

### 👤 صفحه مدیریت

```
https://your-domain/login
```

پس از ورود:
- `/admin` - پنل تنظیمات
- `/admin/config.json` - تنظیمات JSON
- `/admin/ADD.txt` - IP های سفارشی
- `/admin/cf.json` - اطلاعات Cloudflare
- `/admin/log.json` - لاگ‌ها

### 📱 بهینه‌سازی آنلاین IP

1. وارد پنل مدیریت شوید
2. به بخش "بهینه‌سازی آنلاین" بروید
3. کتابخانه IP را انتخاب کنید
4. تست را اجرا کنید
5. بهترین IP ها را ذخیره کنید

---

## 📁 ساختار فایل‌ها

```
SFSD/
├── nvless.js           # کد اصلی Worker
├── index.html          # صفحه اصلی
├── admin/
│   ├── index.html      # پنل مدیریت
│   ├── config.json     # تنظیمات پیش‌فرض
│   └── log.json        # لاگ‌ها
├── login/index.html    # صفحه ورود
├── noKV/index.html    # خطای عدم وجود KV
├── noADMIN/index.html # خطای عدم وجود ADMIN
├── cdn-cgi/trace      # فایل Trace
└── sub/               # مسیر اشتراک
```

---

## ⚙️ تنظیمات پیش‌فرض

```json
{
  "协议类型": "vless",
  "传输协议": "ws",
  "Fingerprint": "chrome",
  "TLS分片": "Shadowrocket",
  "随机路径": false,
  "ECH": false,
  "优选订阅生成": {
    "local": true,
    "SUBNAME": "Nova Proxy"
  }
}
```

---

## 🔧 تنظیمات پیشرفته

### ECH (Encrypted Client Hello)
برای فعال‌سازی ECH:
1. متغیر `ECH` را `true` تنظیم کنید
2. یک دامنه با DoH تنظیم کنید

### SOCKS5 Proxy
```
SOCKS5=username:password@host:port
```

### IP پروکسی سفارشی
در پنل admin > IP های سفارشی یا `ADD.txt`

---

## 📊 منابع IP

### حالت محلی (Local)
- از GitHub دریافت می‌شود:
  - `cmliu/CF-CIDR` - IP های رسمی Cloudflare
  - IP های اپراتورهای چین (CMCC, CU, CT)

### حالت API خارجی
- می‌توانید از API های مختلف استفاده کنید
- در تنظیمات `SUB` وارد کنید

---

## 🙏 تشکر و قدردانی

- [cmliu](https://github.com/cmliu) - منابع IP و API
- [ACL4SSR](https://github.com/ACL4SSR) - کانفیگ Subconverter
- [Cloudflare](https://cloudflare.com) - زیرساخت Workers

---

## 📝 لایسنس

این پروژه برای استفاده شخصی و آموزشی است.

---

<p align="center">
  <a href="https://github.com/IRNova/Nova Proxy">🌟 Star us on GitHub</a>
</p>
