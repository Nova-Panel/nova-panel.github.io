# Nova Worker — Panel

پنل مدیریت **Nova Worker** — نسخه **Beta-0.0.1** — عرضه **آبان ۱۴۰۵**

## مخزن‌ها

| بخش | مخزن |
| --- | --- |
| پنل (این پروژه) | https://github.com/Nova-Panel/nova-panel.github.io |
| Worker | https://github.com/IRNova/NovaWorker |

## انتشار پنل روی GitHub Pages

1. محتویات پوشهٔ `Panel/` را در ریشهٔ مخزن `Nova-Panel/nova-panel.github.io` قرار دهید (فایل‌های قدیمی مثل `nova-admin.js`، `version.json`، `user/` و `sync-test.tmp` را حذف کنید).
2. در تنظیمات مخزن، بخش **Pages**، یکی از دو حالت زیر را انتخاب کنید:
   - **Deploy from a branch** → شاخهٔ `main` و پوشهٔ `/ (root)`؛ یا
   - **GitHub Actions** → ورک‌فلوی آماده در `.github/workflows/static.yml` با هر push روی `main` منتشر می‌کند.
3. آدرس نهایی: `https://nova-panel.github.io`

فایل `.nojekyll` موجود است تا GitHub Pages فایل‌ها را بدون پردازش Jekyll منتشر کند.

## اتصال Worker به پنل

Worker به‌طور پیش‌فرض پنل را از `https://nova-panel.github.io` می‌خواند. برای دامنه‌ی دیگر، متغیر `PANEL_URL` را روی Worker تنظیم کنید:

```toml
[vars]
PANEL_URL = "https://nova-panel.github.io"
```

اگر پنل و Worker در یک پروژه‌ی Cloudflare Pages باشند، بایندینگ `ASSETS` اولویت دارد و نیازی به `PANEL_URL` نیست.

## مسیرها

- `/admin` — پنل مدیریت (نیازمند ورود)
- `/login` — ورود با رمز مدیریت
- `/install` — راه‌اندازی اولیه
- `/sub` — اشتراک
- `/version` — نسخه‌ی Worker

## نحوهٔ دسترسی

- پنل را همیشه از دامنهٔ Worker باز کنید: `https://<worker-domain>/admin`
- آدرس `https://nova-panel.github.io` فقط میزبان فایل‌های پنل است؛ صفحهٔ ورودِ آن، دامنهٔ Worker را می‌پرسد و در مرورگر ذخیره می‌کند.
- اگر پنل مستقیماً روی دامنهٔ استاتیک باز شود، به‌جای نمایش پنل ناقص، پیام راهنما نمایش داده می‌شود.

## ساختار

```
Panel/
├─ index.html            صفحهٔ ورود (ثبت دامنهٔ Worker)
├─ admin/index.html      پنل مدیریت (تک‌فایل، i18n داخلی)
├─ install/index.html    راه‌اندازی اولیه
├─ login/index.html      ورود
├─ manifest.json         PWA
├─ logo*.svg|png         نشان برند
├─ admin/vendor/leaflet  نقشه
└─ .github/workflows     انتشار خودکار GitHub Pages
```

## زبان‌ها

فارسی (RTL)، انگلیسی و روسی. تغییر زبان از نوار کناری پنل انجام می‌شود و در مرورگر ذخیره می‌گردد.

## امنیت

- صفحه‌ی پنل با `noindex, nofollow` منتشر می‌شود.
- احراز هویت با کوکی `HttpOnly` و رمز مدیریت انجام می‌شود.
- داده‌های حساس (کلیدها و توکن‌ها) فقط در KV ورکر نگهداری می‌شوند.
