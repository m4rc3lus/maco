

## Ensuring Script Performance in the Background

When a browser tab is inactive or minimized (including when running on a VPS), the script may slow down significantly. To prevent this, use the following trick:

1. Right-click the browser shortcut and select <b>'Properties'</b>.
2. In the <b>'Target'</b> field, add the following flag at the end of the existing text: <b>`--disable-background-timer-throttling`</b>
<br>(Ensure there's a space between the existing text and the new flag. e.g. `...\chrome.exe" --disable-background-timer-throttling`)
```bash
--disable-background-timer-throttling
```
4. Launch the browser using this modified shortcut.

<b>Note:</b> This method only works for Chromium-based browsers!
