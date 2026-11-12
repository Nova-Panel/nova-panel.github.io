const fs=require("fs");
const t=fs.readFileSync("index.html","utf8");
const i=t.indexOf('id="exp"');
console.log(JSON.stringify(t.slice(i-20,i+560)));
