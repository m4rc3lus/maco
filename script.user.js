// ==UserScript==
// @name         QOL tool
// @version      3.66.3
// @description  Personal passion project, not to share
// @include      https://www.the-west.*
// @include      https://*.the-west.*/game.php*
// @icon         https://westsk.innogamescdn.com/images/items/animal/item_51460.png?7
// @grant        GM_setValue
// @grant        GM_getValue
// @grant        GM_deleteValue
// @grant        GM_info
// @grant        unsafeWindow
// ==/UserScript==
(function() {
    'use strict';
    const MAX_ALLOWED_JOBS = 16; // Maximum jobs handled by expensive Held-Karp algorithm.
    const AUTO_START_DELAY = 6000; // How many milisecons to wait after auto refresh.
    const ENERGY_WASTE_TOLERANCE = 5; // Energy above full energy loss tolerance (consumable %).
    const FUNCTION_TIMEOUT = 5000; // Timeout for equip set attempt and other functions longer than expected execution.
    const EQUIP_TIMEOUT = 10000; // Timeout for preventing potentional hang when equipping multiple gear pieces.
    const NETWORK_CHECK_PERIOD = 10000; // How often would check internet connection in case of connection lost.
    const SESSION_EXPIRE_SECOND = 30; // Delay margin to avoid premature reload.
    const MIN_DUEL_PROTECTION = 30; // Minimum minutes of duel protection remaining for automatic money deposit.
    const BATTLE_MAX_DURATION = 65; // Force signal 'battle end' after specified time in minutes to prevent softlock when original signal is lost.
    const BATTLE_START_MARGIN = 60; // Stop HP refill attempt before battle timeleft (in seconds).
    const BATTLE_BUFF_OVERWRITE_TOLERANCE = 0.25; // Maximum buff duration portion amount allowed to be wasted.
    const GAME_LOAD_TIMEOUT = 20000; // Timeout when to consider game to be stuck in loading screen.
    var battle_time_reserve = 240; // Time added on top of the minimal required fort battle preparation time (in seconds).

    var idle_limit = 10; // Minutes of inactivity to force auto refresh.
    var interval_long = 1000; // Performance interval for checking conditions in loops.
    var interval_short = 500;
    var timeout_long = 4000;
    var timeout_regular = 2000; // Standard safe wait time between various in-game actions.
    var timersAdjusted = false;

    var avg_interval_margin = 1800; // Minimum average of 5 consecutive browser throttling interval measures
    var single_interval_margin = 400; // Minimum measured interval for all 5 measurements
    var timerTestTimeoutId = null;
    var intervalTimeTestLength = 1200000;

    var startStopDelayTimeoutId = null;
    var flagCheckInterval = null;
    var queueAnimationObserver = null;
    var reloadObserverInterval = null;

    var queuedActions = [];
    var isQueueInProgress = false;
    var isRequestInProgress = false;
    var walkToJob_running = false;
    var runJob_running = false;
    var useConsumable_running = false;
    var useBuff_running = false;
    var equipBestGear_running = false;
    var errorOccured = false;
    var characterId = 0;

    const Maco = {
        version:'3.66.3',
        base_url: '',//'https://username.github.io/maco/',
        updateInfo:[],
        updateCheck: function() {
            fetch(Maco.base_url + "update.txt?" + new Date().getTime())
                .then(response => response.text())
                .then(text => {
                    const lines = text.split("\n");
                    const updateInfo = [];
                    let changelog = [];
                    let currentVersionFound = false;
                    let currentVersion = Maco.version;
                    let version = null;

                    lines.forEach(line => {
                        line = line.trim();
                        if (!line) return; // Skip empty lines

                        if (line.toLowerCase().startsWith('version') || line.toLowerCase().startsWith('version:')) { // Match a version keyword
                            if (version != null) updateInfo.push({ version, changelog }); // Store the previous version before resetting
                            version = line.split(/\s*[:\s]\s*/)[1]; // Extract the version number (split by space or colon)
                            changelog = []; // Reset changelog for the new version
                        } else {
                            changelog.push(line); // Add changelog entries for the current version
                        }
                    });

                    if (version != null) updateInfo.push({ version, changelog }); // Ensure the last found version is added, even if no changelog exists
                    Maco.updateInfo = updateInfo;
                    const updates = updateInfo.filter(info => isNewerVersion(currentVersion, info.version)); // Filter for versions higher than the current script version

                    if (updates.length > 0) {
                        let changelogText = updates
                            .filter(info => info.changelog.length > 0) // Ignore empty changelogs
                            .map(info => `
                                <div style='display: flex; gap: 5px; margin-top: 10px;'>
                                    <strong style='display: inline-block; vertical-align: top; min-width: 55px;'>${info.version}</strong>
                                    <div style='display: inline-block;'>
                                        ${info.changelog.map(change => `
                                            <div style='display: flex; gap: 5px;'>
                                                <span style='display: inline-block;'>-</span>
                                                <span>${change}</span>
                                            </div>
                                        `).join("")}
                                    </div>
                                </div>
                            `).join("");

                        const $content = $("<div style='max-width: 450px;'>").append(`<div>A new version is available! Please update.</div>`);

                        if (changelogText.trim() !== "") {
                            $content
                                .append("<div style='margin-top: 15px; font-weight: bold;'>Changelog:</div>")
                                .append(changelogText);
                        }

                        new west.gui.Dialog("Maco &nbsp;&nbsp;" + Maco.version + "&nbsp; &#8594; &nbsp;" + updates[0].version, $content, west.gui.Dialog.SYS_WARNING)
                            .addButton("Update", function() {
                                window.open(Maco.base_url + 'script.user.js');
                                Maco.needReload = true;
                                document.removeEventListener("visibilitychange", Maco.handleVisibilityChange);
                                document.addEventListener("visibilitychange", Maco.handleVisibilityChange);
                            })
                            .show();
                    }
                })
                .catch(error => {console.error("Error fetching update:", error)});
        },
        window:null,
        needReload:false,
        invalidSession:false,
        jobsLoaded:false,
        startTime:null,
        lastReloadTime:null,
        lastResult:[],
        lastResultFarming:[],
        bonusTypeMap:[],
        //skillTexts:[],
        //battleBonusesTexts:[],
        allConsumables:[],
        allJobs:[],
        uniqueJobs:[],
        lastPosition:{x:null, y:null},
        addedJobsOld:[],
        addedJobsHasChanged:true,
        jobsBestGear:[],
        allianceForts:[],
        battles:[],
        towns:[],
        homeTown:null,
        jobsTablePosition:{content:"0px", scrollbar:"0px"},
        addedJobsTablePosition:{content:"0px", scrollbar:"0px"},
        consumablesTablePosition:{content:"0px", scrollbar:"0px"},
        favoriteJobsTablePosition:{content:"0px", scrollbar:"0px"},
        questsTablePosition:{content:"0px", scrollbar:"0px"},
        _currentState: 0,
        get currentState() {
            return this._currentState;
        },
        set currentState(value) {
            if (this._currentState !== value) {
                this._currentState = value;
                handleStateChange(value);
            }
        },
        states:["idle", "running", "waiting for a consumable cooldown", "sleep regenerating", "starting..", "fort battle", "awaiting jobs reset", "town building"],
        lastActiveTab:"jobs",
        xpJobsPreset:[202,205,201,192,204,200,199,185,187,196,180,189,203,181,194,153,197,190,177,188,182,195,184,152,186,191,178,176,159,175,170,193,179,151,165,160,172,161,174,145,183,168,171,147,166,157,149,150,167,164],
        moneyJobsPreset:[193,199,202,185,179,205,204,203,161,190,198,187,200,201,196,181,184,178,182,197,177,191,171,194,168,175,166,192,160,186],
        wayTimes:null,
        wardrobe:new Map(),
        maxHealthForSet:new Map(),
        sets:new Map(),
        selectedSet:null,
        maxAllowedEnergy:100, // in %
        isDuelProtected:false,
        consumableSelection:{energy:false, motivation:false, health:false, buffs:false},
        isRunning:false,
        jobRunning:false,
        energyCost:1,
        language:"",
        translationLang:"",
        // Local storage saved
        addedJobs:[],
        consumablesSelection:[],
        jobsFarmingGear:[],
        favoriteJobs:[],
        dailyQuests:{enabled:true, quests:[]},
        workerProfiles:{selected:"profile0", profile0:{jobs:[], maxJobRank:10, jobsToAdd:8}, profile1:{jobs:[], maxJobRank:10, jobsToAdd:8}, profile2:{jobs:[], maxJobRank:10, jobsToAdd:8}},
        travelSet:-2,
        jobSet:-1,
        healthSet:-3,
        regenerationSet:-1,
        sortJobTable:{xp:1, distance:0, money:0},
        jobFilter:{filterOnlySilver:true, filterNoSilver:false, filterCenterJobs:false, filterFavorites:false, filterEnoughLP:false, filterJob:""},
        farmingAssistant:{enabled:false, jobSwapped:false, stopLevel:false, awaitNextSession:false, selectedGearLevel:0},
        currentJob:{jobIdx:0, direction:true},
        build:{allowed:true, nightBuild:false, interval:900, hoursAmount:6, building:'church', set:-1},
        settings:{
            allowMotivationOptional:false,
            addEnergyOptional:true,
            addEnergy:true,
            addMotivation:true,
            addHealth:true,
            addBuffs:false,
            addXpBuff:false,
            addLuckBuff:false,
            addMoneyBuff:false,
            addProductBuff:false,
            addTravelBuff:true,
            healthStopPercent:20,
            healthStopValue:800,
            addEnergyOptionalMin:15,
            addEnergyOptionalMax:60,
            enableRegeneration:true,
            altTown:null,
            autoMoneyDeposit:{enabled: true, amount: 200000, duelProtected: true, sellerName:"", auctionItemId: ""},
            fortBattle:{attend:false, selected:-1, attackSet:-1, defSet:-1, openFortWindow:false, refillHealth:true, isTank:false, minHealth:100, useConsumable:false, overwriteCharacterBonus:false, consumable:null},
            notifications:{enabled:true, silent:false, requireInteraction:true, error:true, stopped:true, sleep:true, battle:true, battle_prep:false, duel:true},
            autoReload:true,
            autoLogin:true,
            nightShiftWorker:true,
            advancedWalkingToJob:false,
            maxJobRank:10,
            jobsToAdd:8,
            skipTutorial:true,
            allowWardrobeExport:true,
            showMenuIcon: false
        },
        diagnostics:{reloadReasons:[], waitingReasons:[], consumablesUsed:[], errorLog:[]},
        stats: {
            session:{consumableWaitingTime:0, sleepTime:0, travelTime:0, runTime:0, money:0, jobs:0, xp:0},
            total:{money:0, jobs:0, xp:0}
        },
        searchKeys:{
            "en_DK": {
                motivationEventBuff:"Work motivation"
            },
            "sk_SK": {
                motivationEventBuff:"pracovná motivácia"
            },
            "cs_CZ": {
                motivationEventBuff:"pracovní motivace"
            },
            "pl_PL": {
                motivationEventBuff:"motywacji do prac"
            },
            "hu_HU": {
                motivationEventBuff:"munka motiváció"
            },
            "ro_RO": {
                motivationEventBuff:"Motivatie de muncă"
            },
            "tr_TR": {
                motivationEventBuff:"çalışma motivasyonu"
            },
            "nl_NL": {
                motivationEventBuff:"Arbeidsmotivatie"
            },
            "it_IT": {
                motivationEventBuff:"Motivazione lavoro"
            },
            "el_GR": {
                motivationEventBuff:"Κίνητρο δουλειάς"
            },
            "fr_FR": {
                motivationEventBuff:"de motivation de travail"
            },
            "es_ES": {
                motivationEventBuff:"Motivacion de trabajo"
            },
            "de_DE": {
                motivationEventBuff:"Arbeitsmotivation"
            },
            "pt_PT": {
                motivationEventBuff:"motivação de trabalho"
            },
            "pt_BR": {
                motivationEventBuff:"Em motivação para trabalho"
            },
            "ru_RU": {
                premiumText:"Премиум",
                motivationEventBuff:"Восстановление мотивации к работам"
            },
        },
        explainerTranslations:{
            "en_DK": {
                explainer_1: "Continuously replenish energy with consumables that fall within the set min-max energy range (will not use consumables that also add motivation). (Tip: Metal bottle plug = 30% energy every 10 minutes.)",
                explainer_2: "Replenish health if it drops below a certain value and percentage (e.g., if HP falls below 500 and is also less than 20% of total health).",
                explainer_3: "Allows the script to run 24/7. Automatically switches silver jobs based on the 'Rank' order saved in the 'Worker' section. (Also collects the login bonus.) (It may not work properly in browsers such as 'Epic Privacy browser'!)",
                explainer_4: "Use buffs for the character (duration-based) and for traveling (use-based). Select buffs allowed in the 'Consumables' section.",
                explainer_5: "Allow automatic page refresh (F5) if necessary.",
                explainer_6: "Allow to change clothes and assign jobs during travel to save a few insignificant seconds :D",
                explainer_7: "Do not deposit money in the bank while duel protection is active.",
                explainer_8: "Automatically participate in upcoming fort battles and change into the selected set. After the battle ends, job clicking will resume. (Before the battle, it won't replenish energy that cannot be used in time.)",
                explainer_9: "Replenish health before battle if the current health in battle gear is lower than the specified percentage.",
                explainer_10: "After the battle starts, keep the battle window open (stay online).",
                explainer_11: "If unable to replenish energy/motivation/health, at least go regenerate. Will regenerate in closest fort or in closest town.",
                explainer_12: "Use consumable if the motivation of all Added jobs drops to the 'Stop motivation' level. (Tip: Cake decorations + Metal bottle plugs = saved Tinctures.)",
                explainer_13: "Add every silver job on the list up to this specified rank. (It will ignore max jobs limit.)",
                explainer_14: "Maximum jobs amount. Will continue adding additional silver jobs from the list until this specified amount is added.",
                explainer_15: "Saves currently equipped gear as the best ones to equip when starting this job.",
                explainer_16: "Export all saved settings, jobs, sets and consumables to a file, and the ability to re-import the saved data. (Useful, for example, when changing or clearing web browser.)",
                explainer_17: "Set 0 to never stop for motivation refill.",
                explainer_18: "Allocates more time for HP refill. Can also use Fort Medicine if selected in 'Consumables'. (If needed, allows HP to be refilled with two consumables in a row.)",
                explainer_19: "Automatically deposit money in the bank when selected amount is reached.",
                explainer_20: "Waits until the night reset of job motivations and then the script starts working. (It may not work properly in browsers such as 'Epic Privacy browser'!)",
                explainer_21: "Stops upon reaching a new level or daily jobs reset. (Useful, for example, when different clothing needs to be saved at each level to maintain ~0 LP.)",
                explainer_22: "Select a level for which to save the currently worn items. The script will equip these items only if job motivation > 0 and character level < 10. (Default will be used in all other cases.)",
                explainer_23: "Exports saved clothing for the current job to a file and allows for re-importing saved outfits. (Useful, for example, when changing or clearing web browser.)",
                explainer_24: "Enables helper functions for farming products. Designed primarily for accounts up to level 10 (possibly up to 20).",
                explainer_25: "Delay start (in minutes).",
                explainer_26: "Enable 'Night shift worker' setting to build church for 6 hours over night and then continue with jobs. With disabled worker, it will keep building church.",
                explainer_27: "Save a backup town for money deposit before battle.",
                explainer_28: "Enable town build as backup option. Construction can also serve as an alternative activity in cases where the saved jobs do not provide enough silver ones, or as an option for building overnight.",
                explainer_29: "Alternating between jobs and construction. Similar to the 'Night Shift worker' setting, but instead of continuing with jobs, it will first build for a specified number of hours and resume doing jobs after.",
                explainer_30: "During continuous energy replenishment, also allow consumables that can add motivation. (Not recommended. Useful only if there aren't enough better consumables.)",
                explainer_31: "Replace active character buffs with new bonuses, such as HP refill using Fort Medicine.",
                explainer_32: "To deposit money into auction bid instead, specify item ID and seller name."
            },
            "sk_SK": {
                explainer_1: "Dopĺňať energiu priebežne posilneniami, ktoré sa nachádzajú v stanovenom rozsahu % pridanej energie min - max (nepoužije posilnenia ktoré pridávajú aj motiváciu). (Tip: Kovové zátky na fľašu = 30% energie kažých 10 minút.)",
                explainer_2: "Doplniť zdravie v prípade že klesne pod určitú hodnotu a zároveň pod určitý počet percent (napr. ak má menej ako 500 HP a zároveň je to aj menej ako 20% z celkového zdravia).",
                explainer_3: "Umožní scriptu fungovať 24/7. Automaticky vymení strieborné práce podľa poradia 'Rank', ako sú uložené v sekcii 'Worker'. (Vyzdvihne aj prihlasovací bonus.) (V prehliadačoch ako napr. 'Epic Privacy browser', nemusí fungovať správne!)",
                explainer_4: "Používať aj posilnenia pre postavu (na trvanie) a cestovanie (na použitia). Vyberie z posilnení 'Buffs' povolených v sekcii 'Consumables'.",
                explainer_5: "Povoliť automatické znovu načítanie stránky (F5) ak to bude potrebné..",
                explainer_6: "Prezliecť a zadať práce už počas cestovania pre ušetrenie pár bezvyznamných sekúnd :D",
                explainer_7: "Neukladať peniaze do banky pokiaľ je duelová ochrana aktívna.",
                explainer_8: "Automaticky sa zúčasní nadchádzajúceho boja o pevnosť a prezlečie vybraný set. Po skončení boja bude pokračovať v klikaní prác. (Pred bojom nebude dopĺnať energiu, ktorú by nestihol využiť.)",
                explainer_9: "Doplniť zdravie pred bojom, ak aktuálne zdravie v bojovom oblečení je menšie ako počet stanovených percent.",
                explainer_10: "Po začatí boja, nechať bojové okno otvorené (online stav).",
                explainer_11: "V prípade že nebude mať čím doplniť energiu/motiváciu/zdravie, tak pôjde aspoň regenerovať. Regenerovať pôjde do najbližšej pevnosti, alebo najbližšieho mesta.",
                explainer_12: "Použiť posilnenie ak motivácia všetkých pridaných prác klesne na úroveň 'Stop motivation'. (Tip: Tortové ozdoby + Kovové zátky na fľašu = ušetrené Tinktúry.)",
                explainer_13: "Vyberie každú striebornú prácu v zozname až do tohto maximálneho ranku. (Bez ohľadu na maximálny počet prác vpravo.)",
                explainer_14: "Maximálny počet prác. Bude pokračovať vo vyberaní dalších strieborných prác zo zoznamu, pokiaľ ich nebude pridaných tento počet.",
                explainer_15: "Uloží aktuálne oblečené veci ako ako tie najlepšie, ktoré bude obliekať pri začínaní tejto práce.",
                explainer_16: "Export všetkých uložených nastavení, prác, setov a posilnení do súboru a možnosť spätného importovania uložených dát. (Užitočné napr. pri zmene/čistení prehliadača.)",
                explainer_17: "Nastav 0 aby sa nikdy nezastavil a nedopĺňal motiváciu.",
                explainer_18: "Na doplnenie HP si vyhradí viacej času. Môže použiť aj Pevnostnú medicínu, ak je zvolená v 'Consumables'. (Podľa potreby umožní doplniť dvoma HP posilneniami po sebe.)",
                explainer_19: "Pravidelne ukladať peniaze do banky po našetrení zvolenej sumy.",
                explainer_20: "Počká do nočného reštartu motivácie prác a až potom začne script pracovať. (V prehliadačoch ako napr. 'Epic Privacy browser', nemusí fungovať správne!)",
                explainer_21: "Po dosiahnutí nového levelu / dennom resete prác sa zastaví. (Užitočné napr. ak po každom leveli treba uložiť iné oblečenie pre udržanie ~0 PB.)",
                explainer_22: "Zvoliť level, pre ktorý uložiť aktuálne oblečené veci. Script bude obliekať tieto veci len ak je pracovná motivácia > 0 a level postavy < 10. (Default použije v každom inom prípade.)",
                explainer_23: "Export uloženého oblečenia pre aktuálnu prácu do súboru a možnosť spätného Importovania uložených oblečení. (Užitočné napr. pri zmene/čistení prehliadača.)",
                explainer_24: "Sprístupní pomocné funkcie pre farmenie produktov. Navrhnuté najmä pre účty do levelu 10 (prípadne aj do 20).",
                explainer_25: "Oneskoriť štart/stop (počet minút).",
                explainer_26: "Pri zapnutom nastavení 'Night shift worker', bude stavať kostol 6 hodín cez noc a potom bude pokračovať v klikaní prác. Pri vypnutom workerovi ostane stavať len kostol.",
                explainer_27: "Uložiť náhradné mesto pre ukladanie peňazí pred bojom o pevnosť.",
                explainer_28: "Povoliť možnosť výstavby mesta. Výstavba môže slúžiť aj ako alternatívna činnosť v prípadoch, kedy z uložených prác nebude dostatok strieborných, alebo ako možnosť stavania cez noc.",
                explainer_29: "Striedanie prác a výstavby. Obdoba nastavenia 'Night Shift worker', ale namiesto pokračovania v robení prác, bude najprv určený počet hodín stavať a až potom bude znovu pokračovať v robení prác.",
                explainer_30: "Počas priebežného dopĺňania energie povoliť aj posilnenia, ktoré môžu doplniť aj motiváciu. (Neodporúčam. Užitočné len v prípade, že nie je dostatok lepších posilnení.)",
                explainer_31: "Nahradiť aktívne posilnenie pre postavu novým bonusom napr. doplnenie HP pomocou Pevnostnej medicíny.",
                explainer_32: "Pre uloženie peňazí do aukcie namiesto banky, zadaj ID predmetu a meno predávajúceho hráča."
            },
        },
        alertTranslations:{
            "en_DK": {
                alert_1: "Network connection lost.",
                alert_2: (set) => (Premium.hasBonus('automation') || isWithinRange(Array.from(Maco.sets.keys()).indexOf(set), 0, 2))
                    ? "<span style=\"color: red;\">ERROR</span>: Deleted set is still assigned.. Reassign all 'Sets'!"
                    : "<span style=\"color: red;\">ERROR</span>: Deleted set is still assigned.. <span style=\"color: blue;\">'Automation'</span> premium ended.",
                alert_3: "<span style=\"color: orange;\">WARNING</span>: Set can't be equipped.. <span style=\"color: blue;\">'Automation'</span> premium ended.",
                alert_4: (jobName, missingItems) => `Saved gear for '<u>${jobName}</u>' is missing items in inventory: <b>${missingItems}</b>`,
                alert_5: "Can't continue because of motivation.",
                alert_6: "Can't continue because of energy.",
                alert_7: "Can't continue because of health.",
                alert_8: "Could not find any suitable consumable to use.",
                alert_9: "You got KO.",
                alert_10: (jobName) => `Not enough LP to equip Job set for: '<u>${jobName}</u>' ...removing job.`,
                alert_11: "The inactive browser tab caused throttled script timers! <br>Restart browser with flag: <b>--disable-background-timer-throttling</b>",
            },
            "sk_SK": {
                alert_1: "Pripojenie k internetu sa prerušilo.",
                alert_2: (set) => (Premium.hasBonus('automation') || isWithinRange(Array.from(Maco.sets.keys()).indexOf(set), 0, 2))
                    ? "<span style=\"color: red;\">CHYBA</span>: Je priradené odstránené vybavenie.. Znova priraďte všetky 'Sets'!"
                    : "<span style=\"color: red;\">CHYBA</span>: Je priradené odstránené vybavenie.. Skončilo prémium <span style=\"color: blue;\">'Automatizácia'</span>.",
                alert_3: "<span style=\"color: orange;\">WARNING</span>: Vybavenie sa nedá obliecť.. Skončilo prémium <span style=\"color: blue;\">'Automatizácia'</span>.",
                alert_4: (jobName, missingItems) => `Uloženému oblečeniu pre '<u>${jobName}</u>' v inventári chýba: <b>${missingItems}</b>`,
                alert_5: "Nemôže pokračovať kvôli motivácii.",
                alert_6: "Nemôže pokračovať kvôli energii.",
                alert_7: "Nemôže pokračovať kvôli zdraviu.",
                alert_8: "Nenašlo sa žiadne vhodné posilnenie na použitie..",
                alert_9: "Dostal si KO.",
                alert_10: (jobName) => `Pre málo PB nevie obliecť vybavenie na prácu: '<u>${jobName}</u>' ...odstraňujem prácu.`,
                alert_11: "Neaktívne okno prehliadača spôsobuje spomalenie scriptu! <br>Reštartuj prehliadač a použi flag: <b>--disable-background-timer-throttling</b>",
            },
        },
    };

    const globalWindow = (typeof unsafeWindow !== 'undefined') ? unsafeWindow : window;
    //globalWindow.Maco = Maco; // Debugging-only exposure
    /*if (globalWindow.GameMap) {
        Object.defineProperty(globalWindow, 'Maco', {
            value: Maco,
            writable: true,       // or false if you want read-only
            configurable: true,   // allows later deletion
            enumerable: false     // hides from Object.keys(window)
        });
    }*/

    function JobPrototype(x,y,id,groupId,silver) {
        this.x = x;
        this.y = y;
        this.id = id;
        this.groupId = groupId;
        this.silver = silver;
        this.distance = 0;
        this.experience = 0;
        this.money = 0;
        this.motivation = 0;
        this.stopMotivation = 75;
        this.set = -1;
    };
    JobPrototype.prototype = {
        calculateDistance:function() {
            this.distance = Character.calcWayTo({x:this.x, y:this.y});
        },
        setExperience:function(xp) {
            this.experience = xp;
        },
        setMoney:function(money) {
            this.money = money;
        },
        setMotivation:function(motivation) {
            this.motivation = motivation;
        },
        setStopMotivation:function(stopMotivation) {
            this.stopMotivation = stopMotivation;
        },
        setSet:function(setIndex) {
            this.set = setIndex;
        }
    };
    function ConsumablePrototype(id,image,name,bonuses,hasCooldown) {
        this.id = id;
        this.energy = 0;
        this.motivation = 0;
        this.health = 0;
        this.xp = 0;
        this.product = 0;
        this.luck = 0;
        this.money = 0;
        this.travel = 0;
        this.settingTraps = 0;
        this.hiding = 0;
        this.offense = 0;
        this.defense = 0;
        this.battleDamage = 0;
        this.other = 0;
        this.selected = true;
        this.image = image;
        this.count = 0;
        this.duration = 0;
        this.uses = 0;
        this.name = name;
        this.bonuses = bonuses;
        this.hasCooldown = hasCooldown;
        this.hasSpecialBonus = false;
        this.hasCharacterBonus = false;
        this.hasBattleBonus = false;
    };
    ConsumablePrototype.prototype = {
        constructor: ConsumablePrototype,
        setEnergy:function(energy) {
            this.energy = energy;
        },
        setMotivation:function(motivation) {
            this.motivation = motivation;
        },
        setHealth:function(health) {
            this.health = health;
        },
        setXp:function(xp) {
            this.xp = xp || 0;
        },
        setProduct:function(product) {
            this.product = product || 0;
        },
        setLuck:function(luck) {
            this.luck = luck || 0;
        },
        setMoney:function(money) {
            this.money = money || 0;
        },
        setTravel:function(travel) {
            this.travel = travel || 0;
        },
        setOther:function(other) {
            this.other = other || 0;
        },
        setSelected:function(select) {
            this.selected = select;
        },
        setCount:function(count) {
            this.count = count;
        },
        setDuration:function(duration) {
            this.duration = duration || 0;
        },
        setUses:function(uses) {
            this.uses = uses || 0;
        },
        setSpecial:function(special) {
            this.hasSpecialBonus = special;
        },
        setCharacter:function(character) {
            this.hasCharacterBonus = character;
        },
        setBattleItem:function(battle) {
            this.hasBattleBonus = battle;
        },
        setTraps:function(settingTraps) {
            this.settingTraps = settingTraps || 0;
        },
        setHiding:function(hiding) {
            this.hiding = hiding || 0;
        },
        setOffense:function(offense) {
            this.offense = offense || 0;
        },
        setDefense:function(defense) {
            this.defense = defense || 0;
        },
        setBattleDamage:function(damage) {
            this.battleDamage = damage || 0;
        }
    };

    function isNewerVersion(current, latest) {
        const currentParts = current.split('.').map(Number);
        const latestParts = latest.split('.').map(Number);
        for (let i = 0; i < latestParts.length; i++) {
            if ((latestParts[i] || 0) > (currentParts[i] || 0)) return true;
            if ((latestParts[i] || 0) < (currentParts[i] || 0)) return false;
        }
        return false;
    };
    function handleStateChange(newState) {
        Maco.updateStatusIcon();
        Maco.refreshTab("addedJobs");
    };
    function replacer(key, value) { // Custom replacer function for JSON.stringify
        if (value === Infinity) return "Infinity";
        return value;
    };
    function reviver(key, value) { // Custom reviver function for JSON.parse
        if (value === "Infinity") return Infinity;
        return value;
    };
    function debounce(func, defaultDelay = 0) {
        let timeoutId;

        function debounced(...args) {
            let delay = defaultDelay;
            let callback = null;

            if (typeof args[0] === 'number') {
                delay = args.shift(); // Extract delay
            }
            if (typeof args[0] === 'function') {
                callback = args.shift(); // Extract callback
            }

            clearTimeout(timeoutId);

            timeoutId = setTimeout(() => {
                if (callback) callback();
                func.apply(this, args); // Apply remaining arguments to the debounced function
            }, delay);
        }

        debounced.cancel = function() {
            clearTimeout(timeoutId);
        };

        return debounced;
    };
    function wait(duration) {
        return new Promise(resolve => setTimeout(resolve, duration));
    };
    function waitForEvent(eventName, withTimeout = true) {
        return new Promise((resolve) => {
            // Reference to the listener function for unlistening later
            const listener = function () {
                if (withTimeout) clearTimeout(timeout); // Cancel the timeout if the event fires
                resolve();
                return EventHandler.ONE_TIME_EVENT; // Ensure it's a one-time listener
            };

            EventHandler.listen(eventName, listener);

            let timeout;
            if (withTimeout) {
                timeout = setTimeout(() => {
                    EventHandler.unlisten(eventName, listener);
                    resolve(); // Resolve even though the event did not fire
                }, FUNCTION_TIMEOUT);
            }
        });
    };
    function executeQueuedActions() {
        isQueueInProgress = true;
        while (queuedActions.length > 0) {
            let action = queuedActions.shift();
            action();
        }
        isQueueInProgress = false;
    };
    function removeUiElement(key) {
        const element = document.getElementById(key);
        if (element) {
            element.style.display = "none";
            try {
                element.remove();
            } catch (e) {
                const msg = `Exception occured in 'removeUiElement()' while removing DOM element ${key}: `;
                console.error(msg, e.stack);
                Maco.handleError(e, msg, true);
            }
        }
    };
    function customEncode(str) {
        // Step 1: Replace spaces with hyphens
        let result = str.replace(/ /g, '-');

        // Step 2: First encodeURIComponent
        result = encodeURIComponent(result);

        // Step 3: Manually encode '%' as '%25' in case it was already encoded
        result = result.replace(/%/g, '%25');

        return result;
    };
    function assignObjects(target, source) {
        for (const key in source) {
            if (target.hasOwnProperty(key)) {
                const sourceValue = source[key];
                const targetValue = target[key];
                if (typeof targetValue === "object" && typeof sourceValue === "object" && targetValue != null && sourceValue != null) {
                    Object.assign(targetValue, sourceValue); // Merge objects
                } else {
                    target[key] = sourceValue; // Overwrite value
                }
            }
        }
    };
    function normalizeStr(str) {
        str = str.toLowerCase();

        // Remove punctuation
        str = str.replace(/[.,\/#!$%\^&\*;:{}=\-_`~()]/g, "");

        // Normalize diacritics
        str = str.normalize("NFD").replace(/[\u0300-\u036f]/g, "");
        str = str.trim();
        return str;
    };
    function levenshteinDistance(a, b) {
        const an = a ? a.length : 0;
        const bn = b ? b.length : 0;
        if (an === 0) {
            return bn;
        }
        if (bn === 0) {
            return an;
        }
        const matrix = Array.from(Array(bn + 1), () => new Array(an + 1).fill(0));
        for (let i = 0; i <= an; i++) {
            matrix[0][i] = i;
        }
        for (let j = 0; j <= bn; j++) {
            matrix[j][0] = j;
        }
        for (let j = 1; j <= bn; j++) {
            for (let i = 1; i <= an; i++) {
                const cost = a[i - 1] === b[j - 1] ? 0 : 1;
                matrix[j][i] = Math.min(
                    matrix[j - 1][i] + 1,       // deletion
                    matrix[j][i - 1] + 1,       // insertion
                    matrix[j - 1][i - 1] + cost // substitution
                );
            }
        }
        return matrix[bn][an];
    };
    function compareStrings(str1, str2, tolerance = 0.95) {
        const normStr1 = normalizeStr(str1);
        const normStr2 = normalizeStr(str2);
        const distance = levenshteinDistance(normStr1, normStr2);
        const maxLen = Math.max(normStr1.length, normStr2.length);
        const similarity = 1 - distance / maxLen;
        return similarity >= tolerance;
    };
    function formatNumber(number) {
        return number.toString().replace(/\B(?=(\d{3})+(?!\d))/g, '.'); // Format the number with thousands separators
    };
    function clamp(value, min, max) {
        return Math.min(Math.max(value, min), max);
    };
    function isWithinRange(value, min, max) {
        return value >= min && value <= max;
    };
    function getFormattedLocalDate(time = true) {
        // Get the current local date
        var now = new Date();

        // Extract day, month, and year in local time
        var day = String(now.getDate());
        var month = String(now.getMonth() + 1).padStart(2, '0');
        var year = now.getFullYear();

        // Format the date as "day.month.year"
        var formattedDate = day + '.' + month + '.' + year;

        // If time is true, append the time in "hours:minutes" format
        if (time) {
            var hours = String(now.getHours());
            var minutes = String(now.getMinutes()).padStart(2, '0');
            formattedDate += ' ' + hours + ':' + minutes;
        }

        return formattedDate;
    };
    function getUTCDate() {
        function removeFirstWordFromEnd(str) {
            const words = str.split(' ');
            words.pop(); // Remove the last word
            return words.join(' ');
        }

        let utcDate = new Date().toUTCString();
        utcDate = removeFirstWordFromEnd(utcDate);
        return new Date(utcDate);
    };
    function formatTime(seconds, useShortFormat = true, padWithZero = false) {
        if (useShortFormat) {
            if (seconds >= 3600) {
                const hours = Math.floor(seconds / 3600);
                return `${hours}h`;
            } else if (seconds >= 60) {
                const minutes = Math.floor(seconds / 60);
                return `${minutes}m`;
            } else {
                return `${seconds}s`;
            }
        } else {
            const padZero = (num) => (num < 10 ? '0' : '') + num;

            const hours = Math.floor(seconds / 3600);
            const minutes = Math.floor((seconds % 3600) / 60);
            const remainingSeconds = (seconds % 60).toFixed(0);

            return padWithZero ?
                `${padZero(hours)}:${padZero(minutes)}:${padZero(remainingSeconds)}` :
                `${hours}:${padZero(minutes)}:${padZero(remainingSeconds)}`;
        }
    };
    function timestamp(customDate = null) {
        let currentTime;
        if (customDate instanceof Date) {
            currentTime = customDate;
        } else {
            currentTime = new Date();
        }
        const hours = currentTime.getHours().toString().padStart(2, '0');
        const minutes = currentTime.getMinutes().toString().padStart(2, '0');
        const seconds = currentTime.getSeconds().toString().padStart(2, '0');
        // Format day.month.year
        const day = currentTime.getDate().toString();
        const month = (currentTime.getMonth() + 1).toString();
        const year = currentTime.getFullYear().toString();
        const date = `${day}.${month}.${year}`;
        // Format day month
        const monthNames = ['Jan.', 'Feb.', 'Mar.', 'Apr.', 'May', 'Jun.', 'Jul.', 'Aug.', 'Sep.', 'Oct.', 'Nov.', 'Dec.'];
        const monthName = monthNames[currentTime.getMonth()];
        const dayMonth = `${day}. ${monthName}`;

        if (customDate instanceof Date && customDate.getFullYear() !== new Date().getFullYear()) {
            return `${hours}:${minutes}:${seconds} (${date})`;
        } else {
            return `${hours}:${minutes}:${seconds} (${dayMonth})`;
        }
    };
    function calculateElapsedSeconds(startTime) {
        const endTime = new Date();
        const elapsedTime = endTime - startTime; // in milliseconds
        const elapsedSeconds = Math.floor(elapsedTime / 1000); // in seconds
        return elapsedSeconds;
    };
    function extractNumberFromString(str) {
        const regex = /\d+/;
        const match = str.match(regex);
        return match ? parseInt(match[0]) : null;
    };
    function isNaturalNumber(num) {
        return Number.isInteger(num) && num >= 0;
    };
    function isNumber(potentialNumber) {
        return Number.isInteger(parseInt(potentialNumber));
    };
    function isVersionOutdated(current, required) {
        if (!current) return true; // No version means outdated
        const curParts = current.split('.').map(Number);
        const reqParts = required.split('.').map(Number);

        for (let i = 0; i < reqParts.length; i++) {
            if ((curParts[i] || 0) < reqParts[i]) return true;  // current < required
            if ((curParts[i] || 0) > reqParts[i]) return false; // current > required
        }
        return false; // They are equal
    };
    function getReferer() {
        return Game?.gameURL || globalWindow.location.origin;
    };
    function generateRandomNumber(min, max) {
        var minN = Math.min(min, max);
        var maxN = Math.max(min, max);
        return Math.floor((minN + Math.random() * (maxN-minN + 1)));
    };
    function normalizeChatMessage(msg) {
        if (!msg) return "";

        return msg
            .replace(/\/\d{1,3}/g, "")   // remove /111 /999 color codes
            .replace(/\s*\*\s*/g, "")    // remove any * used for formatting
            .trim()
            .replace(/\s+/g, " ");       // normalize spaces
    };
    function proxyMethod(obj, methodName, handler) {
        const original = obj[methodName];
        if (typeof original !== 'function' || typeof Proxy !== 'function') return;
        if (original.__isProxied) return; // Prevent double-proxying

        const proxied = new Proxy(original, {
            apply(target, thisArg, args) {
                return handler({ target, thisArg, args });
            }
        });

        proxied.__isProxied = true;
        obj[methodName] = proxied;
    };
    (function setupChatController() {
        if (typeof Chat !== "object") return;
        function proxyMethod(obj, methodName, handler) {
            const original = obj[methodName];

            obj[methodName] = function (...args) {
                try {
                    const result = handler({ target: original, thisArg: this, args });
                    if (result !== undefined) return result;
                } catch (err) {
                    console.error("[Maco proxy error]", err);
                }
                return original.apply(this, args);
            };
        };
        proxyMethod(Chat, "sendMessage", ({ target, thisArg, args }) => {
            const [message, room] = args;

            if (typeof message === "string") {
                const clean = normalizeChatMessage(message);

                if (/^[\/\\!]m(aco)?\b/.test(clean)) {
                    handleMacoChatCommand(clean, room);
                    return false; // block sending to server
                }
            }

            return;
            //return Reflect.apply(target, thisArg, args);
        });

        function handleMacoChatCommand(msg, room) {
            const parts = msg.split(/\s+/);
            const cmd = parts[1]?.toLowerCase() || "";
            const arg = parts[2];
            const delay = Number(arg) || 0;

            switch (cmd) {
                case "start":
                    Maco.loadMapData(() => macoChatStart(delay * 60000));
                    (delay > 0) ? macoReply(room, `[Maco] Script started. Delay: ${delay} min.`) : macoReply(room, `[Maco] Script started.`);
                    break;

                case "stop":
                    Maco.handleButtonStopClick(delay * 60000);
                    (delay > 0) ? macoReply(room, `[Maco] Script stopped. Delay: ${delay} min.`) : macoReply(room, `[Maco] Script stopped.`);
                    break;

                case "":
                case "gui":
                case "menu":
                case "window":
                    toggleGui();
                    break;

                case "set": {
                    // Format: /m set settings.showMenuIcon = true
                    const full = msg.substring(msg.indexOf("set") + 3).trim();
                    const match = full.match(/^([\w\.]+)\s*=\s*(.+)$/);

                    if (!match) {
                        macoReply(room, "[Maco] Usage: /m set <path> = <value>");
                        break;
                    }

                    const path = match[1];
                    const rawValue = match[2];

                    const result = setDeepProperty(Maco, path, rawValue);

                    if (result.ok) {
                        macoReply(room, `[Maco] Updated '${path}' → ${JSON.stringify(result.newValue)}`);
                        Maco.debouncedSaveAll?.(500); // auto-save
                    } else {
                        macoReply(room, `[Maco] Could not set '${path}': ${result.reason}`);
                    }

                    break;
                }

                default:
                    macoReply(room,
                        "Commands:\n" +
                        "/m start\n" +
                        "/m stop\n" +
                        "/m gui"
                    );
            }
        }

        function setDeepProperty(obj, path, rawValue) {
            const parts = path.split(".");
            let target = obj;

            // Traverse path
            for (let i = 0; i < parts.length - 1; i++) {
                if (!(parts[i] in target)) {
                    return { ok: false, reason: `Property '${parts[i]}' does not exist.` };
                }
                target = target[parts[i]];
            }

            const key = parts[parts.length - 1];
            if (!(key in target)) {
                return { ok: false, reason: `Property '${key}' does not exist.` };
            }

            // Convert value to JS type
            let value;
            if (rawValue === "true") value = true;
            else if (rawValue === "false") value = false;
            else if (rawValue === "null") value = null;
            else if (!isNaN(rawValue)) value = Number(rawValue);
            else value = rawValue; // string

            // Set the value
            target[key] = value;
            return { ok: true, newValue: value };
        }

        function macoChatStart(delay) {
            if (Maco.addedJobs.length === 0 && !Maco.swapSilverJobs()) {
                new UserMessage("No jobs to run.", UserMessage.TYPE_ERROR).show();
                return;
            }
            if (!Maco.setsAssigned()) {
                new UserMessage("Job set not assigned!", UserMessage.TYPE_ERROR).show();
                Maco.createWindow();
            }
            if (!Maco.setCheck()) {
                Maco.showAlert(Maco.alertTranslations[Maco.translationLang].alert_2(0));
            }

            Maco.handleScriptStart(delay);
        }

        function toggleGui() {
            try {
                //if (Maco.window && Maco.window.isOpen()) {
                  //  Maco.window.close();
                //} else {
                    Maco.loadMapData(Maco.createWindow);
                //}
            } catch (e) {
                console.error("toggleGui error:", e);
            }
        }

        function macoReply(room, text) {
            Chat.pushSystemMessage(`${text}`, false, room);
        }

        function notify(text) {
            new UserMessage(text, UserMessage.TYPE_SUCCESS).show();
        }
    })();
    // The game has annoying bug when consumables are on cooldown and page refreshes.. just to prevent console error spam..
    globalWindow.onerror = function(message, source, lineno, colno, error) {
        let errorMessage = '', errorStack = '', errorSource = source, errorLine = lineno, errorObj = error;

        if (typeof message === 'object') { // Handle sandboxed context (all in `message`)
            errorMessage = message.message || '';
            errorStack = message.error?.stack || '';
            errorSource = message.filename || '';
            errorLine = message.lineno || 0;
            errorObj = message.error;
        } else { // Normal context
            errorMessage = message || '';
            errorStack = error?.stack || '';
        }

        if (errorStack.includes('updateCooldownTimer')) {
            //console.log("Clearing all cooldown intervals in 'BuffList.cooldowns' to prevent console error spam.");
            const cooldowns = BuffList.cooldowns;
            Object.keys(cooldowns).forEach((id) => {
                if (cooldowns[id]?.timer) {
                    globalWindow.clearInterval(cooldowns[id].timer);
                }
            });

            return true; // Return true to prevent the error from being logged to the console
        }

        const scriptName = GM_info.script.name;
        if (errorSource.includes(customEncode(scriptName)) || errorSource.includes(encodeURIComponent(scriptName))) {
            Maco.handleError(errorObj);
        }

        return false; // Allow other handlers to process error
    };
    function waitForCondition(conditionFn, callback, checkInterval = 500, timeout = 10000, alwaysCallback = false) {
        const startTime = Date.now();

        function check() {
            if (conditionFn()) {
                callback();
            } else if (Date.now() - startTime < timeout) {
                setTimeout(check, checkInterval);
            } else if (alwaysCallback) {
                callback();
            }
        }

        check();
    };
    Maco.startTimerTestLoop = function() {
        function runTest() {
            Maco.testTimerThrottling({title:"Timer test.", bad:true, good:false}).then((isThrottled) => {
                Maco.adjustGlobalTimings(isThrottled);
                scheduleNextTest(); // Schedule the next test after the current one completes
            });
        }

        function scheduleNextTest() {
            clearTimeout(timerTestTimeoutId);
            timerTestTimeoutId = setTimeout(runTest, intervalTimeTestLength); // Store timeout ID
        }

        scheduleNextTest(); // Start the initial test
    };
    Maco.cancelTimerTestLoop = function() {
        clearTimeout(timerTestTimeoutId); // Cancels the timeout
        if (Maco.debouncedTestTimerThrottling.cancel) {
            Maco.debouncedTestTimerThrottling.cancel();
        }
    };
    Maco.debouncedTestTimerThrottling = debounce((logResults) => {
        if (document.visibilityState === 'hidden' || document.hidden) {
            Maco.testTimerThrottling(logResults).then((isThrottled) => {
                const isDocumentHidden = document.visibilityState === 'hidden' || document.hidden;
                Maco.adjustGlobalTimings(isThrottled && isDocumentHidden);
                if (isThrottled && isDocumentHidden && logResults.title === "Confirm Timer test.") {
                    Maco.showAlert(Maco.alertTranslations[Maco.translationLang].alert_11, true, null, () => {
                        avg_interval_margin = 8000;
                        single_interval_margin = 1000;
                    });
                }
            });
        }
    }, 10000);
    Maco.adjustGlobalTimings = function(throttled = false) {
        if (throttled && !timersAdjusted) {
            console.log("%cMaco Timings adjusted.", "color:orange");
            Maco.debouncedTestTimerThrottling({title:"Confirm Timer test.", bad:false, good:false});
            Maco.startTimerTestLoop();
            timersAdjusted = throttled;
            idle_limit = 15;
            battle_time_reserve = 360;
        } else if (!throttled && timersAdjusted) {
            console.log("%cMaco Timings restored.", "color:green");
            Maco.cancelTimerTestLoop();
            timersAdjusted = throttled;
            idle_limit = 10;
            battle_time_reserve = 240;
        }
    };
    Maco.testTimerThrottling = function(logResults = {title:"", bad:true, good:false}, interval = 100) {
        return new Promise((resolve) => {
            const avgIntervalMargin = avg_interval_margin + interval + 1800;
            const singleIntervalMargin = single_interval_margin + interval + 400;
            const numTests = 5; // Number of intervals to measure
            let expectedNextTime = performance.now() + interval;
            let measuredIntervals = [];

            function checkTimer() {
                let now = performance.now();
                let elapsed = now - (expectedNextTime - interval);

                measuredIntervals.push(elapsed);

                if (measuredIntervals.length < numTests) {
                    expectedNextTime += interval;
                    setTimeout(checkTimer, Math.max(0, expectedNextTime - performance.now()));
                } else { // Results
                    measuredIntervals.splice(0, 1);
                    const averageInterval = measuredIntervals.reduce((acc, cur) => acc + cur, 0) / measuredIntervals.length;
                    const isFullyThrottled = measuredIntervals.every(t => t > singleIntervalMargin);

                    if (averageInterval > avgIntervalMargin && isFullyThrottled) {
                        if (logResults.bad) {
                            console.log(`%c${logResults.title} ${timestamp()}\n` +
                                `Measured intervals: ${measuredIntervals.map(t => t.toFixed(2)).join(', ')}.\n` +
                                `Average interval: ${averageInterval.toFixed(2)} ms. (expected: ${interval}).`, 'color: orange'
                            );
                        }
                        resolve(true);
                    } else {
                        if (logResults.good) {
                            console.log(`%c${logResults.title} ${timestamp()}\n` +
                                `Average interval: ${averageInterval.toFixed(2)} ms. (expected: ${interval}).`, 'color: green'
                            );
                        }
                        resolve(false);
                    }
                }
            }
            checkTimer();
        });
    };
    Maco.installHooks = function() {
        const MAX_WAIT_TIME = AUTO_START_DELAY - 1000; // Maximum wait time in ms
        const CHECK_INTERVAL = 100;
        let elapsedTime = 0;

        const checkAndInstallHooks = () => {
            const functionsReady =
                typeof Player?.forceLogout === "function" &&
                typeof ItemUse?.use === "function" &&
                typeof TaskQueue?.handleError === "function" &&
                typeof Premium?.checkForPremium === "function" &&
                typeof TaskQueue?.handlePlayerDeath === "function" &&
                typeof Ajax?.remoteCall === "function" &&
                typeof MarketWindow?.Sell?.collectAll === "function" &&
                //typeof LinearQuestHandler?.init === "function" &&
                typeof Trader?.buyDialog === "function" &&
                typeof west?.wof?.WofHeartsWindow?.prototype?.animateRewards === "function";

            if (functionsReady || elapsedTime >= MAX_WAIT_TIME) {
                const originalForceLogout = Player?.forceLogout;
                const originalItemUse = ItemUse?.use;
                const originalTaskError = TaskQueue?.handleError;
                const originalPremiumCheck = Premium?.checkForPremium;
                const originalHandlePlayerDeath = TaskQueue?.handlePlayerDeath;
                const originalRemoteCall = Ajax?.remoteCall;
                const originalMarketCollect = MarketWindow?.Sell.collectAll;
                const originalTraderDialog = Trader?.buyDialog;
                const originalAnimateRewards = west?.wof.WofHeartsWindow.prototype.animateRewards;
                //const originalQuestHandler = LinearQuestHandler?.init;

                /*if (Maco.settings.skipTutorial) {
                    LinearQuestHandler.init = new Proxy(originalQuestHandler, {
                        apply(target, thisArg, argumentsList) {
                            EventHandler.signal("tutorial_finished");
                            return Reflect.apply(target, thisArg, argumentsList);
                        }
                    });
                }*/

                proxyMethod(Ajax, "remoteCall", ({ target, thisArg, args }) => {
                    const [window, action, param, callback, view] = args;
                    const wrappedCallback = function(data) {
                        if (window === 'inventory' && action === 'switch_equip' && data.error) {
                            EventHandler.signal('equip_error', data.msg);
                        }
                        if (typeof callback === 'function') {
                            callback(data);
                        }
                    };
                    return Reflect.apply(target, thisArg, [window, action, param, wrappedCallback, view]);
                });

                if (Maco.getActiveEventId()) {
                    west.wof.WofHeartsWindow.prototype.animateRewards = new Proxy(originalAnimateRewards, {
                        apply(target, thisArg, args) {
                            const [prize, newPrizes] = args;

                            $(".reward_container .item").removeClass("overlay");

                            var slot = thisArg.getSlotByItemId(prize.itemId);
                            var reward = $(".reward_" + slot);
                            var classChange = thisArg.getColor(reward.data('itemId'));
                            reward.addClass('overlay');
                            reward.removeClass(classChange);

                            GameGift.enqueue("wof", [prize.itemId, thisArg.wof.prizes.enhanceToColor(prize.itemEnhance)], function() {});
                            if (newPrizes) {
                                thisArg._initRewards(newPrizes);
                            }
                            thisArg.paySpin.enable();

                            return;
                        }
                    });
                }

                proxyMethod(Ajax, "remoteCall", ({ target, thisArg, args }) => {
                    const [window, action, param, callback, view] = args;
                    const wrappedCallback = function(data) {
                        if (window === 'inventory' && action === 'switch_equip' && data.error) {
                            EventHandler.signal('equip_error', data.msg);
                        }
                        if (typeof callback === 'function') {
                            callback(data);
                        }
                    };
                    return Reflect.apply(target, thisArg, [window, action, param, wrappedCallback, view]);
                });

                Player.forceLogout = new Proxy(originalForceLogout, {
                    apply(target, thisArg, argumentsList) {
                        Maco.invalidSession = true;
                        const reloadInfoString = Maco.localStorageGet('reloadData');
                        if (!reloadInfoString && Maco.isRunning) {
                            Maco.setReloadData("Invalid session. ");
                        }

                        return Reflect.apply(target, thisArg, argumentsList);
                    }
                });

                proxyMethod(Premium, "checkForPremium", ({ target, thisArg, args }) => {
                    const [bonus, callback] = args;
                    if (bonus === "energy") {
                        return false;
                    }
                    return Reflect.apply(target, thisArg, args);
                });

                proxyMethod(TaskQueue, "handleError", ({ target, thisArg, args }) => {
                    const [task, error, msg] = args;
                    EventHandler.signal('task_error', msg);
                    return Reflect.apply(target, thisArg, args);
                });

                proxyMethod(Trader, "buyDialog", ({ target, thisArg, args }) => {
                    const result = Reflect.apply(target, thisArg, args);

                    const [item_id] = args;
                    const item = Trader.getItemByItemId(item_id);

                    setTimeout(() => {
                        const dialog = $(".tw2gui_dialog_framefix");
                        if (!dialog.length) return result;
                        const actionsContainer = dialog.find(".tw2gui_dialog_actions");
                        if (!actionsContainer.length) return result;

                        const textfield = new west.gui.Textfield("buyAmount_textfield", null, 'manual_input').onlyNumeric().setValue(1).setWidth(40);
                        const textfieldDiv = textfield.getMainDiv();
                        $(textfieldDiv).css({
                            display: "inline-block",
                            position: "relative",
                            marginRight: "5px",
                        });

                        const textfieldDelay = new west.gui.Textfield("delay_textfield", null, 'manual_input').onlyNumeric().setValue(1000).setPlaceholder("delay").setWidth(40);
                        const textfieldDelayDiv = textfieldDelay.getMainDiv().css({
                            display: "inline-block",
                            position: "relative",
                        });

                        const delayWrapper = $("<div class='delay-wrapper'></div>").css({
                            display: "inline-block", // Initially hidden
                            position: "relative",
                            float: "left"
                        });
                        delayWrapper.append("<span class='delay-text'>delay:</span>");
                        delayWrapper.append(textfieldDelayDiv);
                        delayWrapper.append("<span class='ms-text'>ms</span>");

                        const yesButton = actionsContainer.find(".tw2gui_button").first();
                        yesButton.off("click").on("click", function () {
                            if (textfield.getValue() > 1) {
                                dialog.remove();
                                Maco.traderBuy(item, textfield.getValue(), textfieldDelay.getValue());
                            } else {
                                dialog.remove();
                                Trader.buyItem(item);
                            }
                        });

                        const secondButton = actionsContainer.find(".tw2gui_button").eq(1);
                        if (secondButton.length > 0) {
                            actionsContainer.prepend(textfieldDiv);
                            actionsContainer.prepend(delayWrapper);
                            delayWrapper.hide();
                        }

                        $("#buyAmount_textfield").on("input", function () {
                            if (parseInt(textfield.getValue()) > 1) {
                                delayWrapper.show(); // Show if value > 1
                            } else {
                                delayWrapper.hide(); // Hide otherwise
                            }
                        });
                    }, 0);

                    return result;
                });

                proxyMethod(ItemUse, "use", ({ target, thisArg, args }) => {
                    const [itemId, bonuses, type] = args;

                    const result = Reflect.apply(target, thisArg, args);

                    const item = Bag.getItemByItemId(itemId);
                    if (item.obj.has_cooldown !== false || item.count <= 1 || item.obj.usetype == "use") return result;

                    setTimeout(() => {
                        const dialog = $(".tw2gui_dialog_framefix");
                        if (!dialog.length) return result;
                        const actionsContainer = dialog.find(".tw2gui_dialog_actions");
                        if (!actionsContainer.length) return result;

                        const textfield = new west.gui.Textfield("useAmount_textfield", null, 'manual_input').onlyNumeric().setValue(1).setWidth(40);
                        const textfieldDiv = textfield.getMainDiv();
                        $(textfieldDiv).css({
                            display: "inline-block",
                            position: "relative",
                            marginRight: "5px",
                        });

                        const textfieldDelay = new west.gui.Textfield("delay_textfield", null, 'manual_input').onlyNumeric().setValue(1000).setPlaceholder("delay").setWidth(40);
                        const textfieldDelayDiv = textfieldDelay.getMainDiv().css({
                            display: "inline-block",
                            position: "relative",
                        });

                        const delayWrapper = $("<div class='delay-wrapper'></div>").css({
                            display: "inline-block", // Initially hidden
                            position: "relative",
                            float: "left"
                        });
                        delayWrapper.append(textfieldDelayDiv);
                        delayWrapper.append("<span class='ms-text'>ms</span>");

                        const maxButton = $("<button>")
                            .text(`(${item.count})`)
                            .on("click", function () {
                                textfield.setValue(item.count); // Set text field value to item.count
                                delayWrapper.show();
                            })
                            .css({
                                position: "relative", verticalAlign: "middle", marginRight: "2px", marginBottom: "1.5px", padding: "0",
                                background: "none", border: "none", cursor: "pointer", fontWeight: "bold", fontSize: "14px", lineHeight: "0.1"
                            })
                            .addClass("linkstyle");

                        const yesButton = actionsContainer.find(".tw2gui_button").first();
                        yesButton.off("click").on("click", function () {
                            if (textfield.getValue() > 1) {
                                dialog.remove();
                                Maco.useItemLoop(item, textfield.getValue(), textfieldDelay.getValue());
                            } else {
                                setTimeout(() => {
                                    dialog.remove();
                                    ItemUse.doIt(itemId);
                                }, 200);
                            }
                        });

                        const secondButton = actionsContainer.find(".tw2gui_button").eq(1);
                        if (secondButton.length > 0 && document.querySelector('.tw2gui_window.inventory')) {
                            actionsContainer.prepend(textfieldDiv);
                            actionsContainer.prepend(maxButton);
                            actionsContainer.prepend(delayWrapper);
                            delayWrapper.hide();
                        }

                        $("#useAmount_textfield").on("input", function () {
                            if (parseInt(textfield.getValue()) > 1) {
                                delayWrapper.show(); // Show if value > 1
                            } else {
                                delayWrapper.hide(); // Hide otherwise
                            }
                        });
                    }, 0); // Timeout ensures DOM modifications occur after the dialog is rendered

                    return result;
                });

                proxyMethod(MarketWindow.Sell, "collectAll", ({ target, thisArg, args }) => { // (Premium.confirmUse) can be used as alternative for cancelling multiple premium dialogs at once
                    const [window] = args;

                    let errorTown = false;

                    const refreshList = function () {
                        if (errorTown) {
                            new MessageError(errorTown).show();
                            return true;
                        }
                        EventHandler.signal('inventory_changed');
                        MarketWindow[window].initData();
                    };

                    const action = (window === 'Sell') ? 'fetch_town_offers' : 'fetch_town_bids';

                    Ajax.remoteCall('building_market', action, {}, function (resp) {
                        errorTown = resp.error ? resp.msg : false;
                        if (!resp.error) {
                            Character.setDeposit(resp.deposit);
                            Character.setMoney(resp.cash);
                            return new MessageSuccess(resp.msg).show();
                        }
                    }, MarketWindow).done(function () {
                        refreshList();
                    });

                    // No return value expected from original function
                });

                proxyMethod(TaskQueue, "handlePlayerDeath", ({ target, thisArg, args }) => {
                    const [lastDied, previousDeath, isInit, isFirstKO] = args;

                    if (isInit) {
                        return Reflect.apply(target, thisArg, args);
                    }

                    Ajax.remoteCallMode('task', 'get_tasks', {}, function (resp) {
                        TaskQueue.init(resp.queue);
                        Maco.handleDeath();
                    });
                });

                if (elapsedTime >= MAX_WAIT_TIME) { // #TEST
                    console.warn(`Maco: Proxies installed. Max wait time (${MAX_WAIT_TIME}ms) reached. Some hooks may be missing.`);
                } else {
                    console.log(`Maco: Proxies installed. Elapsed time: ${elapsedTime}ms.`);
                }
            } else {
                elapsedTime += CHECK_INTERVAL;
                setTimeout(checkAndInstallHooks, CHECK_INTERVAL);
            }
        };

        checkAndInstallHooks();
    };
    Maco.traderBuy = async function(item, amount, delay) {
        for (let i = 0; i < amount; i++) {
            if (item.obj.price > Character.getCapital()) {
                break;
            }
            Trader.buyItem(item);
            await wait(delay);
        }
    };
    Maco.addRunTimeEventListeners = function() {
        //EventHandler.listen('fort_battle_joined', Maco.updateFortBattles);
        document.addEventListener("visibilitychange", Maco.handleVisibilityChange);
        globalWindow.addEventListener('offline', Maco.handleNetworkChange);
        //window.addEventListener('blur', Maco.handleWindowBlur);
    };
    Maco.removeRunTimeEventListeners = function() {
        Maco.cancelTimerTestLoop();
        //EventHandler.unlisten('fort_battle_joined', Maco.updateFortBattles);
        document.removeEventListener("visibilitychange", Maco.handleVisibilityChange);
        globalWindow.removeEventListener('offline', Maco.handleNetworkChange);
        globalWindow.removeEventListener('online', Maco.handleNetworkChange);
        //globalWindow.removeEventListener('blur', Maco.handleWindowBlur);
        //globalWindow.removeEventListener('focus', Maco.handleWindowFocus);
    };
    Maco.handleVisibilityChange = function() {
        if (document.visibilityState === 'hidden' || document.hidden) {
            Maco.debouncedTestTimerThrottling({title:"Document is hidden.", bad:true, good:false});
        } else {
            Maco.adjustGlobalTimings();
            if (Maco.needReload) {
                globalWindow.location.reload();
            }
        }
    };
    /*Maco.handleWindowBlur = function() {
        setTimeout(() => {
            if (!document.hidden) {
                Maco.debouncedTestTimerThrottling({title:"Window focus lost.", bad:true, good:false});
                globalWindow.addEventListener('focus', Maco.handleWindowFocus, { once: true });
            }
        }, 100);
    };
    Maco.handleWindowFocus = function() {
        console.log('Window gained focus - ' + timestamp());
        Maco.adjustGlobalTimings();
    };*/
    Maco.handleNetworkChange = function() {
        const status = navigator.onLine ? "online" : "offline";
        console.log(`Network status changed: You are currently ${status}.`);
        if (!navigator.onLine) {
            Maco.showAlert(Maco.alertTranslations[Maco.translationLang].alert_1);
            globalWindow.addEventListener('online', Maco.handleNetworkChange, { once: true });
        }
    };
    Maco.handleDeath = function() {
        if (![4,5].includes(Maco.currentState)) {
            Maco.showAlert(Maco.alertTranslations[Maco.translationLang].alert_9);
        }

        setTimeout(function () {
            Maco.cancelSleep();
        }, timeout_regular);
    };
    Maco.cancelSleep = function(any = false) {
        if (TaskQueue.queue.length > 0 && ['sleep', 'fortsleep'].includes(TaskQueue.queue.at(0).type) && Object.keys(TaskQueue.toCancel).length === 0 &&
            (Maco.isDestinationReached(Maco.homeTown) || any) && Maco.currentState !== 3
        ) {
            TaskQueue.cancel(0);
        }
    };
    Maco.handleError = function(err, msg = "", logOnly = false) {
        errorOccured = !logOnly;

        const errorDetails = {
            error: msg + err.name + ": " + err.message,
            stack: err.stack,
            timestamp: getFormattedLocalDate()
        };

        if (Character && (!Maco.diagnostics.errorLog.length || (Maco.diagnostics.errorLog[0]?.error !== errorDetails.error && Maco.diagnostics.errorLog[0]?.stack !== err.stack))) {
            Maco.diagnostics.errorLog.unshift(errorDetails);
            if (Maco.diagnostics.errorLog.length > 20) {
                Maco.diagnostics.errorLog.pop();
            }
            Maco.debouncedSaveAll(0);
        }
    };
    Maco.startReloadObserver = function() {
        const DESTINY_TIMEOUT = 300000 // 5 minutes
        let destinyCount = 0;
        let destinyCountTimeoutId = null;
        let lastLoggedMinute = 0;
        let errorMessage = "Got stuck";

        if (Maco.startTime == null) {
            Maco.startTime = new Date();
        }
        if (reloadObserverInterval) {
            clearInterval(reloadObserverInterval);
        }

        reloadObserverInterval = setInterval(function() {
            const wayData = TaskQueue.queue.at(0)?.wayData ?? {};
            const travelTime = wayData.date_done - wayData.date_start || 0; // Travel time to substract from elapsedMinutes
            const lastUpdateTime = Maco.startTime.getTime() + travelTime;
            const currentTime = new Date().getTime();
            const elapsedMinutes = Math.floor((currentTime - lastUpdateTime) / (1000 * 60)); // minutes
            const criticalError = document.querySelector('.critical-error');

            if ((elapsedMinutes >= idle_limit && [1].includes(Maco.currentState)) || criticalError || (Maco.invalidSession && elapsedMinutes > 2)) {
                if (criticalError) {
                    if (++destinyCount > 2) {
                        setTimeout(() => {
                            errorMessage = "Critical error (maybe destiny?). ";
                            Maco.reload(errorMessage);
                        }, DESTINY_TIMEOUT);
                        Maco.handleButtonStopClick();
                    } else {
                        clearTimeout(destinyCountTimeoutId);
                        destinyCountTimeoutId = setTimeout(() => {
                            destinyCount = 0;
                        }, DESTINY_TIMEOUT);
                        const dialog = criticalError.closest('.tw2gui_dialog.system_error');
                        const buttons = dialog.querySelectorAll('.tw2gui_button');
                        buttons[buttons.length - 1].click();
                    }
                    return;
                } else if (Maco.invalidSession) {
                    Maco.saveAll();
                    if (Maco.relogAllowed() && Maco.settings.autoReload) {
                        errorMessage = "Invalid session (relogged). ";
                        Maco.relog(errorMessage);
                        return;
                    } else {
                        errorMessage = "Invalid session (reloaded). ";
                    }
                } else {
                    errorMessage += equipBestGear_running ? " while equipping best gear." : walkToJob_running ? " while traveling to job." : runJob_running ? " while running job." : errorOccured ? ", error occured." : " somehow..";
                    if (destinyCount === 0) {
                        errorMessage += " (Idle limit: " + idle_limit + " min.) ";
                    }
                    errorMessage += errorOccured ? "[error]" : `[state:${Maco.currentState}]`;
                }

                if (Maco.settings.autoReload) {
                    Maco.reload(errorMessage);
                }

                lastLoggedMinute = 0;
                clearInterval(reloadObserverInterval);
                return;
            }

            if (elapsedMinutes >= 5 && lastLoggedMinute < elapsedMinutes && ([1].includes(Maco.currentState) || criticalError)) {
                console.log("Last activity " + elapsedMinutes + " minutes ago.. Page will auto refresh in " + (idle_limit - elapsedMinutes) + " minutes.");
                lastLoggedMinute = elapsedMinutes;
            }
        }, 10000);
    };
    Maco.setReloadData = function(reason, auto_start = true) {
        const reasonMsg = reason ? timestamp() + " - " + reason : "";
        const reloadInfo = {
            reason: reasonMsg,
            auto_start: auto_start
        };
        Maco.localStorageSet('reloadData', JSON.stringify(reloadInfo));
        GM_setValue("auto_login", {allowed: auto_start, world: Game.worldName});
    };
    Maco.reload = function(reason, auto_start = true) {
        Maco.setReloadData(reason, auto_start);
        globalWindow.location.reload();
    };
    Maco.relog = function(reason, auto_start = true) {
        Maco.setReloadData(reason, auto_start);
        if (Maco.invalidSession) {
            globalWindow.location.href = Game.masterURL + "/index.php?page=logout";
        } else {
            globalWindow.location.href = "game.php?window=logout&action=logout&h=" + Player.h;
        }
    };
    Maco.relogAllowed = function() {
        const isPermaLogged = GM_getValue("perma_logged", false);
        return Maco.settings.autoLogin && isPermaLogged && characterId !== 0;
    };
    Maco.gameLogin = async function(worldName = '') {
        let worldCheckTimeout = null;

        function parseTimestamp(timestampText) {
            const parts = timestampText.split(' ');
            const dateParts = parts[0].split('-');
            let timeParts = [];
            if (parts.length > 1) {
                timeParts = parts[1].split(':');
            }
            return new Date(dateParts[2], dateParts[1] - 1, dateParts[0], timeParts[0] || 0, timeParts[1] || 0, timeParts[2] || 0);
        }

        function getLatestConnectedWorldName(worldRows) {
            let mostRecentTimestamp = new Date(0);
            let worldToConnect = '';
            for (let i = 0; i < worldRows.length; i++) {
                const row = worldRows[i];
                const timestampText = row.querySelector('.world.last_played > div:nth-child(2)').textContent.trim();
                if (!timestampText) continue;
                const timestamp = parseTimestamp(timestampText);
                if (timestamp > mostRecentTimestamp) {
                    mostRecentTimestamp = timestamp;
                    worldToConnect = row.querySelector('.world.name')?.textContent.trim();
                }
            }
            return worldToConnect;
        }

        function checkWorldRows() {
            const worldRows = document.querySelectorAll('.world_row');
            if (worldRows.length > 0) {
                clearTimeout(loginTimeout);
                const targetWorldName = worldName || getLatestConnectedWorldName(worldRows);

                try {
                    for (let i = 0; i < worldRows.length; i++) {
                        const gameWorld = worldRows[i].querySelector('.world.name');
                        if (gameWorld.textContent.trim() === targetWorldName) {
                            console.log("Choosen server: " + targetWorldName);
                            gameWorld.click();
                            return;
                        }
                    }
                } catch (e) {
                    const msg = "Login error at 'checkWorldRows()': ";
                    console.error(msg, e.stack);
                    Maco.handleError(e, msg, true);
                }
            } else {
                worldCheckTimeout = setTimeout(function() {
                    worldCheckTimeout = null;
                    checkWorldRows();
                }, 500);
            }
        };

        const serverMaintenanceTimeout = setTimeout(function() {
            globalWindow.location.reload();
        }, 3e5); // 5 minutes (6e5 = 10min)

        const loginTimeout = setTimeout(function() {
            clearTimeout(worldCheckTimeout);
            clearTimeout(serverMaintenanceTimeout);
            console.log("Maco could not login within timeout.");
            Maco.showAlert("Could not login. (Login credentials not saved?)");
            return;
        }, 4000);

        //const isPermaLogged = document.querySelector('#cookieLogged') != null;
        const loginButton = document.getElementById('loginButton');

        if (loginButton) {
            console.log("Login attempt " + timestamp());
            loginButton.click();
        } else {
            clearTimeout(loginTimeout);
            clearTimeout(serverMaintenanceTimeout);
            return;
        }

        checkWorldRows();
    };
    Maco.setNewHomeTown = function(pos = Character.position) {
        for (let i = 0; i < Maco.towns.length; i++) {
            if (Maco.towns[i].x === pos.x && Maco.towns[i].y === pos.y) {
                Maco.homeTown = Maco.towns[i];
                Maco.settings.altTown = Maco.homeTown;
                return true;
            }
        }
        return false;
    };
    Maco.filterAllianceForts = function(minForts = 1) {
        const type2Forts = Maco.allianceForts.filter(fort => fort.type === 2); // BIG
        const type1Forts = Maco.allianceForts.filter(fort => fort.type === 1); // Medium

        if (type2Forts.length >= minForts) { // Prefer only type 2 forts if minForts or more exist
            Maco.allianceForts = type2Forts;
        } else { // Include type 2 and type 1 forts
            Maco.allianceForts = [...type2Forts, ...type1Forts];
        }
    };
    Maco.loadMapData = function(callback) {
        if (Maco.jobsLoaded) {
            Maco.updateFortBattles();
            Maco.findAllConsumables();
            //Maco.createWindow();
            Maco.loadSets(function(){});
            if (typeof callback === 'function') {
                callback();
            }
            return;
        }
        new UserMessage("Loading...", UserMessage.TYPE_HINT).show();
        var tiles = [];
        var index = 0;
        var currentLength = 0;
        var maxLength = 299;
        Ajax.get('map','get_minimap', {}, function(r) {
            var tiles = [];
            var jobs = [];
            Maco.allianceForts = [];
            for (var fortNumber in r.forts) {
                for (var fortNumber2 in r.forts[fortNumber]) {
                    var fort = r.forts[fortNumber][fortNumber2];
                    if (Character.homeTown?.town_id != 0 && fort.fort?.alliance_id == Character.homeTown?.alliance_id) {
                       Maco.allianceForts.push(fort['fort']);
                    }
                }
            }
            if (Character.homeTown.town_id != 0) {
                for (var townNumber in r.towns) {
                    if (r.towns[townNumber].member_count !== 0 && r.towns[townNumber].town_id == Character.homeTown.town_id) {
                        Maco.homeTown = r.towns[townNumber];
                        break;
                    }
                }
                Maco.filterAllianceForts();
            } else if (Maco.settings.altTown != null) {
                Maco.homeTown = Maco.settings.altTown;
            } else {
                for (var townNumber in r.towns) {
                    if (r.towns[townNumber].member_count !== 0) {
                        Maco.towns.push({town_id: r.towns[townNumber].town_id, x: r.towns[townNumber].x, y: r.towns[townNumber].y, name: r.towns[townNumber].name});
                        if (Maco.homeTown == null && r.towns[townNumber].x === Character.position.x && r.towns[townNumber].y === Character.position.y) {
                            Maco.homeTown = r.towns[townNumber];
                            Maco.settings.altTown = Maco.homeTown;
                        }
                    }
                }
            }
            Maco.updateFortBattles();
            for (var jobGroup in r.job_groups) {
                const groupId = parseInt(jobGroup);
                var group = r.job_groups[jobGroup];
                var jobsGroup = JobList.getJobsByGroupId(groupId);
                for (var tilecoord = 0; tilecoord < group.length; tilecoord++) {
                    var xCoord = Math.floor(group[tilecoord][0] / GameMap.tileSize);
                    var yCoord = Math.floor(group[tilecoord][1] / GameMap.tileSize);
                    if (currentLength === 0) {
                        tiles[index] = [];
                    }
                    tiles[index].push([xCoord,yCoord]);
                    currentLength++;
                    if (currentLength === maxLength) {
                        currentLength = 0;
                        index++;
                    }
                    for (let i = 0; i < jobsGroup.length; i++) {
                        jobs.push(new JobPrototype(group[tilecoord][0], group[tilecoord][1], jobsGroup[i].id, groupId, false));
                    }
                }
            }

            var toLoad = tiles.length;
            var loaded = 0;

            for (var blocks = 0; blocks < tiles.length; blocks++) {
                GameMap.Data.Loader.load(tiles[blocks], function() {
                    loaded++;
                    if (loaded === toLoad) {
                        for (let i = 0; i < jobs.length; i++) {
                            jobs[i].silver = Maco.checkIfSilver(jobs[i].x, jobs[i].y, jobs[i].id);
                        }
                        for (let i = 0; i < Maco.addedJobs.length; i++) {
                            Maco.addedJobs[i].silver = Maco.checkIfSilver(Maco.addedJobs[i].x, Maco.addedJobs[i].y, Maco.addedJobs[i].id);
                        }
                        Maco.allJobs = jobs;
                        Maco.jobsLoaded = true;
                        Maco.findAllConsumables();
                        //Maco.createWindow();
                        if (typeof callback === 'function') {
                            callback();
                        }
                    }
                });
            }
        });
    };
    Maco.loadJobsData = async function(callback) {
        async function attemptLoadJobsData() {
            try {
                const response = await Ajax.get('work', 'index', {});
                if (response.jobs) {
                    JobsModel.initJobs(response.jobs);
                    callback();
                }
            } catch (e) {
                if (!await Maco.checkInternetConnection()) {
                    if (await Maco.waitForInternetConnection()) {
                        await attemptLoadJobsData();
                    }
                } else {
                    const msg = "Unhandled error in 'Maco.loadJobsData': ";
                    console.error(msg, e.stack);
                    Maco.handleError(e, msg);
                }
            }
        }

        await attemptLoadJobsData();
    };
    Maco.loadSets = (function() {
        let lastLoadTime = 0; // Tracks the last time the Ajax call was made
        const cooldown = 10000; // Cooldown period in milliseconds

        return function (callback) {
            const currentTime = Date.now();
            Maco.wardrobe = new Map(
                (JSON.parse(localStorage.getItem('TWCalc_Wardrobe') || '[]'))
                    .map(item => [item.id, item])
            );

            if (currentTime - lastLoadTime >= cooldown) { // Execute Ajax call if cooldown has expired
                lastLoadTime = currentTime;
                Ajax.remoteCallMode('inventory', 'show_equip', {}, function (r) {
                    Maco.sets = new Map(r.data.map(set => [set.name, set]));
                    if (Maco.selectedSet == null) {
                        Maco.selectedSet = ((r.data.length > 0) ? r.data[0].name : Maco.wardrobe.keys().next().value) ?? Maco.selectedSet;
                    }
                    callback();
                });
            } else { // Skip Ajax call and execute callback immediately
                callback();
            }
        };
    })();
    Maco.loadAccountSettings = function() {
        Ajax.remoteCall("settings", "settings", {})
            .done(function(r) {
                const lang = r.lang?.account?.key || Game.locale;
                Maco.login = r.activities || {}; 
                Maco.language = lang;
                applyLanguageSettings(lang);
            })
            .fail(function() {
                console.error("Failed to load account settings.");
                Maco.login = Maco.login || {}; 
                Maco.language = Game.locale; 

                applyLanguageSettings(Game.locale);
            });

        function applyLanguageSettings(lang) {
            Maco.translationLang = Maco.explainerTranslations[lang] 
                ? lang 
                : (lang === "cs_CZ" ? "sk_SK" : "en_DK");

            characterId = Character.level > 24 ? Character.playerId : 0;
        }
    };
    Maco.verifySilverJobs = async function() {
        for (let i = 0; i < Maco.addedJobs.length; i++) {
            try {
                const isSilver = await Maco.loadJobSilverStatus(i);
                if (!isSilver && Maco.addedJobs[i].silver) {
                    return true;
                }
            } catch (e) {
                const msg = `Error checking job at index ${i} in 'Maco.verifySilverJobs()': `;
                console.error(msg, e.stack || e.message || e);
                Maco.handleError(e, msg);
                break;
            }
        }
        return false;
    };
    Maco.loadJobSilverStatus = function(index) {
        return new Promise((resolve, reject) => {
            Maco.loadJob(index, function(job) {
                if (job != undefined) {
                    resolve(job.is_silver || false);
                } else {
                    reject(new Error("Failed to load job data."));
                }
            }, function(error) {
                reject(error);
            });
        });
    };
    Maco.loadJobMotivation = function(index, callback) {
        Maco.loadJob(index, function(job) {
            callback(Math.floor(job.motivation * 100));
        }, function(error) {
            const msg = "Failed to load job in 'Maco.loadJobMotivation': ";
            console.error(msg, error.stack || error.message || error);
            Maco.handleError(error, msg);
            callback(0); // <— Prevents the chain from freezing
        });
    };
    Maco.loadJob = async function(index, callback, errorCallback) {
        const maxRetries = 2; // Maximum number of retries
        const retryDelay = 2000; // Delay between retries in milliseconds

        async function attemptLoadJob(retryCount = 0) {
            try {
                await Ajax.get('job', 'job', {
                    jobId: Maco.addedJobs[index].id,
                    x: Maco.addedJobs[index].x,
                    y: Maco.addedJobs[index].y
                }, function(json) {
                    callback(json);
                });
            } catch (e) {
                if (!await Maco.checkInternetConnection()) {
                    if (await Maco.waitForInternetConnection()) {
                        await attemptLoadJob();
                    } else if (errorCallback) {
                        errorCallback(e);
                    }
                } else if (retryCount < maxRetries) {
                    console.error(`Error occurred in 'Maco.loadJob'. Retrying (${retryCount + 1}/${maxRetries})...`);
                    await new Promise(resolve => setTimeout(resolve, retryDelay));
                    await attemptLoadJob(retryCount + 1);
                } else {
                    if (errorCallback) {
                        errorCallback(e);
                    } else {
                        const msg = "Unhandled error in 'Maco.loadJob': ";
                        console.error(msg, e.stack || e.message || e);
                        Maco.handleError(e, msg);
                    }
                }
            }
        }

        await attemptLoadJob();
    };
    Maco.checkInternetConnection = function() {
        if (!navigator.onLine) {
            return Promise.resolve(false);
        }
        const url = 'https://www.google.com/favicon.ico';
        const fetchPromise = fetch(url, { method: 'GET', mode: 'no-cors' });
        const timeoutPromise = new Promise((_, reject) =>
            setTimeout(() => reject(new Error('Request Timeout')), FUNCTION_TIMEOUT)
        );
        return Promise.race([fetchPromise, timeoutPromise]) // return the first settled promise (either fetch or timeout)
            .then(() => true)
            .catch(() => false);
    };
    Maco.waitForInternetConnection = function() {
        return new Promise(resolve => {
            const checkConnection = () => {
                Maco.checkInternetConnection().then(isConnected => {
                    if (isConnected) {
                        console.log("Internet connection restored.");
                        resolve(isConnected);
                    } else if (!Maco.isRunning) {
                        resolve(isConnected);
                    } else {
                        console.error("Navigator reports online, but fetch check failed. Still waiting...");
                        setTimeout(checkConnection, NETWORK_CHECK_PERIOD);
                    }
                });
            };

            if (navigator.onLine) {
                checkConnection();
            } else {
                const handleOnline = () => {
                    globalWindow.removeEventListener('online', handleOnline);
                    checkConnection();
                };

                console.error("No internet connection. Waiting to retry...");
                globalWindow.addEventListener('online', handleOnline);
            }
        });
    };
    Maco.getJobName = function(id) {
        return JobList.getJobById(id).name;
    };
    Maco.getJobIcon = function(silver, id, x, y, showExtraIcon = false) {
        const gotoIcon ='<div class="centermap" onclick="GameMap.center(' + x + ',' + y + ');"style="position: absolute; background-image: url(\'../images/map/icons/instantwork.png\'); width:20px; height:20px; top:0; right:3px; cursor:pointer;"></div>';
        const warningIconStyle = 'background: url(/images/tw2gui/iconset.png) repeat -48px 64px; transform: scale(1.0); transformOrigin: center; width: 16px; height: 16px; position: absolute; top: 0; left: 0; margin-top: 1px;';
        const dangerIconStyle = 'background: url(/images/tw2gui/iconset.png) repeat -80px 48px; transform: scale(1.0); transformOrigin: center; width: 16px; height: 16px; position: absolute; top: 0; left: 0; margin-top: 1px;';
        const lockedIconStyle = 'background: url(/images/tw2gui/iconset.png) repeat -32px 112px; transform: scale(1.0); transformOrigin: center; width: 16px; height: 16px; position: absolute; top: 0; left: 0; margin-top: 1px;';
        const job = JobsModel.getById(id);
        const warningIcon = showExtraIcon
            ? !job.jobObj.canDo()
                ? `<span style="${lockedIconStyle}"></span>`
                : job.jobpoints < job.workpoints
                    ? `<span style="${dangerIconStyle}"></span>`
                    : job.jobstarsValue < 6
                        ? `<span style="${warningIconStyle}"></span>`
                        : ''
            : '';
        const silverHtml = silver ? 'silver' : '';
        return'<div class="job" style="left: 0; top: 0; position: relative;"><div onclick="javascript:GameMap.JobHandler.openJob(' + id + ',{x:' + x + ',y:' + y + '})" class="featured ' + silverHtml + '"></div>' + gotoIcon + warningIcon + '<img src="../images/jobs/' + JobList.getJobById(id).shortname + '.png" class="job_icon"></div>';
    };
    Maco.getConsumableIcon = function(item, countText) {
        const src = item.image;

        // Create the DOM structure for inventory item enable popup functionality
        const $wrapper = $("<div class='item item_inventory hasMousePopup'>")
            .css("position", "relative") // just if needed for layout
            .click(() => ItemUse.use(item.id, item.bonuses));

        const $img = $("<img class='tw_item item_inventory_img'>").attr("src", src);
        const $count = $("<span class='count' style='display: block;'>").text(countText);

        $wrapper.append($img).append($count);

        // Add popup functionality using ItemManager
        const popupItem = ItemManager.get(item.id);
        new ItemPopup(popupItem).bindTo($img);

        return $wrapper;
    };
    Maco.findJobData = function(job) {
        for (let i = 0; i < JobsModel.Jobs.length; i++) {
            if (JobsModel.Jobs[i].id === job.id) {
                return JobsModel.Jobs[i];
            }
        }
    };
    Maco.parseJobData = function(jobs) {
        for (const currentJob of jobs) {
            const data = Maco.findJobData(currentJob);
            const { experience: baseXp, money: baseMoney } = data.basis.short;
            const multiplier = currentJob.silver ? 1.5 : 1;

            currentJob.setMotivation(data.jobmotivation * 100);
            currentJob.setExperience(Math.ceil(baseXp * multiplier));
            currentJob.setMoney(Math.ceil(baseMoney * multiplier));
        }
    };
    Maco.updateAllJobDistances = function(jobs = Maco.allJobs) {
        for (let i = 0; i < jobs.length; i++) {
            jobs[i].calculateDistance();
        }
    };
    Maco.checkIfSilver = function(x,y,id) {
        var key = x + "-" + y;
        var jobData = GameMap.JobHandler.Featured[key];
        if (jobData == undefined || jobData[id] == undefined) {
            return false;
        } else {
            return jobData[id].silver;
        }
    };
    Maco.getClosetSilverJob = function(jobid, getSilver = true) {
        Maco.updateAllJobDistances();
        let closestJob = null;
        for (let i = 0; i < Maco.allJobs.length; i++) {
            if (Maco.allJobs[i].id === jobid && (Maco.allJobs[i].silver === getSilver)) {
                if (closestJob == null) {
                    closestJob = Maco.allJobs[i];
                } else if (Maco.allJobs[i].distance < closestJob.distance) {
                    closestJob = Maco.allJobs[i];
                }
            }
        }
        return closestJob;
    };
    Maco.compareUniqueJobs = function(job, jobs) {
        let mapCenter = {x:23000, y:10000};
        for (let i = 0; i < jobs.length; i++) {
            if (jobs[i].id === job.id) {
                if (job.silver && !jobs[i].silver ||
                    (job.silver === jobs[i].silver && (
                        (job.silver && GameMap.calcWayTime(job, mapCenter) < GameMap.calcWayTime(jobs[i], mapCenter)) ||
                        (!job.silver && job.distance < jobs[i].distance)
                    ))) {
                    jobs[i] = job;
                }
                return;
            }
        }
        jobs.push(job);
    };
    Maco.compareNonUniqueJobs = function(job, jobs, isAdded) {
        for (let i = 0; i < jobs.length; i++) {
            if (jobs[i].id === job.id) {
                if (job.silver && !jobs[i].silver || (!job.silver && !jobs[i].silver && job.distance < jobs[i].distance)) {
                    jobs[i] = job;
                } else if (job.silver && (job.distance !== jobs[i].distance && !isAdded)) {
                    break;
                }
                return;
            }
        }
        jobs.push(job);
    };
    Maco.swapSilverJobs = function() {
        if (Maco.favoriteJobs.length === 0) return false;
        const maxJobRank = Math.min(Maco.workerProfiles[Maco.workerProfiles.selected].maxJobRank, Maco.favoriteJobs.length);
        const addedJobIds = new Set(Maco.addedJobs.map(job => job.id));
        let jobs = [];
        let favoriteJobsAdded = 0;

        for (let i = 0; i < Maco.allJobs.length; i++) {
            let currentJob = Maco.allJobs[i];
            if (addedJobIds.has(currentJob.id)) {
                continue;
            }
            Maco.compareUniqueJobs(currentJob, jobs);
        }

        for (let i = 0; i < maxJobRank; i++) {
            const favoriteJob = Maco.favoriteJobs[i];
            if (jobs.some(job => job.id === favoriteJob.id && job.silver) && favoriteJobsAdded <= MAX_ALLOWED_JOBS) {
                const matchingJob = jobs.find(job => job.id === favoriteJob.id && job.silver);
                Maco.addJob(matchingJob.x, matchingJob.y, matchingJob.id);
                favoriteJobsAdded++;
            }
        }

        for (let i = maxJobRank; i < Maco.favoriteJobs.length; i++) {
            const favoriteJob = Maco.favoriteJobs[i];
            if (favoriteJobsAdded >= Maco.workerProfiles[Maco.workerProfiles.selected].jobsToAdd) {
                break;
            }
            if (jobs.some(job => job.id === favoriteJob.id && job.silver)) {
                const matchingJob = jobs.find(job => job.id === favoriteJob.id && job.silver);
                Maco.addJob(matchingJob.x, matchingJob.y, matchingJob.id);
                favoriteJobsAdded++;
            }
        }

        if (favoriteJobsAdded <= 1 && Maco.farmingAssistant.enabled && maxJobRank <= 1 && Math.min(Maco.workerProfiles[Maco.workerProfiles.selected].jobsToAdd, Maco.favoriteJobs.length) === 1) {
            if (Maco.addedJobs.length === 0) {
                const matchingJob = jobs.find(job => job.id === Maco.favoriteJobs[0].id);
                Maco.addJob(matchingJob.x, matchingJob.y, matchingJob.id);
                favoriteJobsAdded++;
            }
            Maco.addedJobs[0].stopMotivation = 0;
        }

        return favoriteJobsAdded > 0 || Maco.addedJobs.length > 0;
    };
    Maco.getAllUniqueJobs = function() {
        let jobs = [];
        if (Maco.favoriteJobs.length === 0) return jobs;
        Maco.updateAllJobDistances();

        for (const currentJob of Maco.allJobs) {
            Maco.compareUniqueJobs(currentJob, jobs);
        }

        return jobs;
    };
    Maco.getUniqueJobs = function() {
        let jobs = [];
        Maco.updateAllJobDistances();
        const addedJobIds = new Set(Maco.addedJobs.map(job => job.id));

        for (const currentJob of Maco.allJobs) {
            Maco.compareNonUniqueJobs(currentJob, jobs, addedJobIds.has(currentJob.id));
        }

        return jobs;
    };
    Maco.getAllFilteredUniqueJobs = function() {
        let jobs = [];
        Maco.updateAllJobDistances();
        const addedJobIds = new Set(Maco.addedJobs.map(job => job.id));

        for (const currentJob of Maco.allJobs) {
            if (!Maco.jobFilterCondition(currentJob, Maco.getJobFilterParams())) continue;

            Maco.compareNonUniqueJobs(currentJob, jobs, addedJobIds.has(currentJob.id));
        }

        Maco.parseJobData(jobs);

        if (Maco.sortJobTable.xp) { // Sorting logic based on experience and distance flags
            jobs.sort((a, b) => Maco.sortJobTable.xp * (b.experience - a.experience));
        } else if (Maco.sortJobTable.distance) {
            jobs.sort((a, b) => Maco.sortJobTable.distance * (b.distance - a.distance));
        } else if (Maco.sortJobTable.money) {
            jobs.sort((a, b) => Maco.sortJobTable.money * (b.money - a.money));
        }

        return jobs;
    };
    Maco.filterUniqueJobs = function(jobs) {
        Maco.updateAllJobDistances(jobs);
        const filteredJobs = jobs.filter(job => Maco.jobFilterCondition(job, Maco.getJobFilterParams()));
        Maco.parseJobData(filteredJobs);

        if (Maco.sortJobTable.xp) { // Sorting logic based on experience and distance flags
            filteredJobs.sort((a, b) => Maco.sortJobTable.xp * (b.experience - a.experience));
        } else if (Maco.sortJobTable.distance) {
            filteredJobs.sort((a, b) => Maco.sortJobTable.distance * (b.distance - a.distance));
        } else if (Maco.sortJobTable.money) {
            filteredJobs.sort((a, b) => Maco.sortJobTable.money * (b.money - a.money));
        }

        return filteredJobs;
    };
    Maco.jobFilterCondition = function(job, { filterText, favoriteJobIds }) {
        return (
            (!filterText || Maco.getJobName(job.id).toLowerCase().normalize("NFD").replace(/[\u0300-\u036f]/g, "").includes(filterText)) &&
            (!Maco.jobFilter.filterFavorites || !favoriteJobIds.has(job.id)) &&
            (!Maco.jobFilter.filterNoSilver || !job.silver) &&
            (!Maco.jobFilter.filterOnlySilver || job.silver) &&
            (!Maco.jobFilter.filterCenterJobs || job.groupId >= 29) &&
            (!Maco.jobFilter.filterEnoughLP || JobList.getJobById(job.id).canDo())
        );
    };
    Maco.getJobFilterParams = function() {
        return {
            filterText: Maco.jobFilter.filterJob.toLowerCase().normalize("NFD").replace(/[\u0300-\u036f]/g, ""),
            favoriteJobIds: new Set(Maco.favoriteJobs.map(favJob => favJob.id))
        };
    };
    Maco.findJob = function(x,y,id) {
        for (let i = 0; i < Maco.allJobs.length; i++) {
            if (Maco.allJobs[i].id === id && Maco.allJobs[i].x === x && Maco.allJobs[i].y === y) {
                return Maco.allJobs[i];
            }
        }
    };
    Maco.addJob = function(x,y,id) {
        if (Maco.checkIfJobAdded(id)) return;
        let job = Maco.findJob(x,y,id);
        const savedJob = Maco.favoriteJobs.find(job => job.id === id);
        if (savedJob) job.setSet(savedJob.set);
        if (job.set === -1) job.setSet(Maco.jobSet);
        if (Character.level <= 19 && Maco.farmingAssistant.enabled) job.setStopMotivation(0);
        Maco.addedJobs.push(job);
        Maco.addedJobsHasChanged = true;
    };
    Maco.removeJob = function(x,y,id) {
        for (let i = 0; i < Maco.addedJobs.length; i++) {
            if (Maco.addedJobs[i].id === id && Maco.addedJobs[i].x === x && Maco.addedJobs[i].y === y) {
                if (Maco.lastResult.length === Maco.addedJobs.length) {
                    Maco.lastResult.splice(i, 1);
                }
                Maco.addedJobs.splice(i, 1);
                Maco.consolidePosition(i);
                Maco.addedJobsHasChanged = true;
                break;
            }
        }
    };
    Maco.consolidePosition = function(removeIndex) {
        if (Maco.currentJob.jobIdx > 0) {
            if (Maco.currentJob.jobIdx === Maco.addedJobs.length) {
                Maco.currentJob.jobIdx--;
            } else if (removeIndex < Maco.currentJob.jobIdx) {
                Maco.currentJob.jobIdx--;
            } else if (removeIndex === Maco.currentJob.jobIdx && !Maco.currentJob.direction) {
                Maco.currentJob.jobIdx--;
            }
        }
        if (Maco.addedJobs.length === 1) {
            Maco.currentJob.direction = true;
        }
    };
    Maco.checkIfJobAdded = function(id) {
        for (let i = 0; i < Maco.addedJobs.length; i++) {
            if (Maco.addedJobs[i].id === id) {
                return true;
            }
        }
        return false;
    };
    Maco.findAddedJob = function(x,y,id) {
        for (let i = 0; i < Maco.addedJobs.length; i++) {
            if (Maco.addedJobs[i].x === x && Maco.addedJobs[i].y === y && Maco.addedJobs[i].id === id) {
                return Maco.addedJobs[i];
            }
        }
        return null;
    };
    Maco.getJobSet = function(x,y,id) {
        const job = Maco.findAddedJob(x,y,id);
        if (job != null)
            return job.set;
    };
    Maco.setJobSet = function(x,y,id,set) {
        const job = Maco.findAddedJob(x,y,id);
        if (job != null)
            return job.setSet(set);
    };
    Maco.setSetForAllJobs = function(set = Maco.jobSet) {
        for (let i = 0; i < Maco.addedJobs.length; i++) {
            if (Maco.addedJobs[i].set === -1 || set === -1) {
                Maco.addedJobs[i].setSet(set);
            }
        }
    };
    Maco.setSetForFavoriteJobs = function(set = Maco.jobSet) {
        for (let i = 0; i < Maco.favoriteJobs.length; i++) {
            if (Maco.favoriteJobs[i].set === -1) {
                Maco.favoriteJobs[i].set = set;
            }
        }
    };
    Maco.updateFavoriteJobs = function(id, selected, newSet = Maco.jobSet) {
        const index = Maco.favoriteJobs.findIndex(job => job.id === id);
        
        if (selected && index === -1) {
            Maco.favoriteJobs.push({ id, set: newSet });
        } else if (!selected && index !== -1) {
            Maco.favoriteJobs.splice(index, 1);
        } else if (selected && index !== -1) {
            Maco.favoriteJobs[index].set = newSet;
        }
    };
    Maco.parseStopMotivation = function() {
        for (let i = 0; i < Maco.addedJobs.length; i++) {
            var stopMotivation = $(".Maco2window #x-" + Maco.addedJobs[i].x + "y-" + Maco.addedJobs[i].y + "id-" + Maco.addedJobs[i].id).prop("value");
            if (isNumber(stopMotivation)) {
                Maco.addedJobs[i].setStopMotivation(clamp(parseInt(stopMotivation), 0, 100));
            } else {
                return false;
            }
        }
        return true;
    };
    Maco.getItemImage = function(id) {
        return ItemManager.get(id).wear_image;
    };
    Maco.BagSearch = function(text) {
        let res = [];

        if (!Bag.loaded) {
            EventHandler.listen('inventory_loaded', function() {
                Maco.findAllConsumables();
                return EventHandler.ONE_TIME_EVENT;
            });
            return res;
        }

        const searchPattern = new RegExp('^.*' + text + '(.*)$', 'i');
        const items = Bag.getItemsByItemIds();

        west.common.forEach(items, function(item, item_id) {
            let obj = item.obj;

            switch (text) {
                case "useable":
                    if (obj.usetype !== 'none' && obj.profession_id == undefined) {
                        res.push(item);
                    }
                    break;
                default:
                    if (searchPattern.test(obj.name) ||
                        (obj.set !== null && searchPattern.test(west.storage.ItemSetManager.get(obj.set).name)) ||
                        Bag.searchAttrib(obj.bonus, searchPattern) ||
                        Bag.searchUseBonus(obj, searchPattern) ||
                        text == obj.level ||
                        (obj.profession !== undefined && searchPattern.test(obj.profession))
                    ) {
                        res.push(item);
                    }
                    break;
            }
        });

        return res;
    };
    Maco.findAllConsumables = function() {
        if (Maco.bonusTypeMap.length === 0) {
            Maco.normalizeSearchKeys(Maco.searchKeys[Maco.language]);
        }
        const oldLength = Maco.allConsumables.length;
        const consumes = Maco.BagSearch("useable");
        const consumeIds = new Set(consumes.map(item => item.obj.item_id));

        // Set count to 0 for items in Maco.allConsumables that are not in inventory anymore
        Maco.allConsumables.forEach(item => {
            if (!consumeIds.has(item.id)) item.count = 0;
        });

        for (let i = 0; i < consumes.length; i++) {
            Maco.addConsumable(consumes[i]);
        }

        if (Maco.allConsumables.length > oldLength) {
            Maco.loadAllConsumablesSelection();
        }
    };
    Maco.checkIfConsumableAdded = function(item) {
        if (item == undefined) return true;

        for (let i = 0; i < Maco.allConsumables.length; i++) {
            if (Maco.allConsumables[i].id === item.obj.item_id) {
                if (Maco.allConsumables[i].count !== item.count) {
                    Maco.allConsumables[i].count = item.count;
                }
                return true;
            }
        }

        return false;
    };
    Maco.normalizeSearchKeys = function(lang) {
        function cleanBonusText(text) {
            text = text.trim();

            // Case: colon detected → keep label up to the colon
            if (text.includes(":")) {
                return text.substring(0, text.indexOf(":") + 1).trim();
            }

            // Remove leading/trailing or standalone numeric parts like "+25%", " 100 ", etc.
            // Regex will match:
            //   - optional + or - (or Unicode minus)
            //   - optional spaces
            //   - number (int or float)
            //   - optional % sign
            //   - optional spaces
            return text
                .replace(/([+\-−]?\s*\d+[.,]?\d*\s*%?)/g, "")
                .replace(/\s+/g, " ")
                .trim();
        }

        try {
            const bonus = {
                energyText: cleanBonusText(ItemManager.get(1890000).usebonus[0]),
                healthText: cleanBonusText(ItemManager.get(1883000).usebonus[0]),
                motivationText: cleanBonusText(ItemManager.get(12701000).usebonus[0]),
                luckText: cleanBonusText(ItemManager.get(2247000).usebonus[0]),
                productText: cleanBonusText(ItemManager.get(2466000).usebonus[0]),
                xpText: cleanBonusText(ItemManager.get(2467000).usebonus[0]),
                moneyText: cleanBonusText(ItemManager.get(2468000).usebonus[0]),
                travelText: cleanBonusText(ItemManager.get(1987000).usebonus[0]),
                durationText: cleanBonusText(ItemManager.get(2467000).usebonus[1]),
                usesText: cleanBonusText(ItemManager.get(1987000).usebonus[1]),
                strengthText: cleanBonusText(ItemManager.get(2287000).usebonus[0]),
                mobilityText: cleanBonusText(ItemManager.get(2287000).usebonus[2]),
                dexterityText: cleanBonusText(ItemManager.get(2287000).usebonus[1]),
                charismaText: cleanBonusText(ItemManager.get(2287000).usebonus[3]),
                hidingText: cleanBonusText(ItemManager.get(54380000).usebonus[1]),
                settingTrapsText: cleanBonusText(ItemManager.get(54381000).usebonus[1]),
                leadershipText: cleanBonusText(ItemManager.get(54382000).usebonus[1]),
                //dodgingText: cleanBonusText(ItemManager.get(54380000).usebonus[0]),
                constructionText: cleanBonusText(ItemManager.get(53940000).usebonus[0]),
                healthPointsText: cleanBonusText(ItemManager.get(54382000).usebonus[0]),
                laborPointsText: cleanBonusText(ItemManager.get(1940000).usebonus[0]),
                battleDamageText: cleanBonusText(ItemManager.get(2741000).usebonus[0]),
                battleAttackText: cleanBonusText(ItemManager.get(2741000).usebonus[2]),
                battleDefendText: cleanBonusText(ItemManager.get(2741000).usebonus[1])
            };

            // Pre-normalize the bonus type map and skill texts
            Maco.bonusTypeMap = [
                { key: normalizeStr(bonus.energyText), type: 0 },
                { key: normalizeStr(bonus.motivationText), type: 1 },
                { key: normalizeStr(bonus.healthText), type: 2 },
                { key: normalizeStr(bonus.xpText), type: 3 },
                { key: normalizeStr(bonus.productText), type: 4 },
                { key: normalizeStr(bonus.luckText), type: 5 },
                { key: normalizeStr(bonus.moneyText), type: 6 },
                { key: normalizeStr(bonus.durationText), type: 8 },
                { key: normalizeStr(bonus.usesText), type: 9 },
                { key: normalizeStr(lang.premiumText ?? 'premium'), type: 10 }, // Every lang translation has same premium text except RU
                { key: normalizeStr(bonus.travelText), type: 11 },
                // skills = type 7
                { key: normalizeStr(bonus.strengthText), type: 7 },
                { key: normalizeStr(bonus.mobilityText), type: 7 },
                { key: normalizeStr(bonus.dexterityText), type: 7 },
                { key: normalizeStr(bonus.charismaText), type: 7 },
                { key: normalizeStr(bonus.constructionText), type: 7 },
                { key: normalizeStr(bonus.leadershipText), type: 7 },
                { key: normalizeStr(bonus.healthPointsText), type: 7 },
                { key: normalizeStr(bonus.laborPointsText), type: 7 },
                // battle buffs = type 12
                { key: normalizeStr(bonus.battleAttackText), type: 12 },
                { key: normalizeStr(bonus.battleDefendText), type: 13 },
                { key: normalizeStr(bonus.battleDamageText), type: 14 },
                { key: normalizeStr(bonus.hidingText), type: 15 },
                { key: normalizeStr(bonus.settingTrapsText), type: 16 }
            ];
        } catch (e) {
            console.error("ItemManager is not initialized yet: ", e.stack);
        }
    };
    Maco.addConsumable = function(item) {
        if (Maco.checkIfConsumableAdded(item)) return;

        const consumable = new ConsumablePrototype(item.obj.item_id, item.obj.image, item.obj.name, item.obj.usebonus, item.obj.has_cooldown);
        const bonuses = Maco.parseConsumableBonuses(item.obj.usebonus);

        if (//bonuses[10] == null || ( // (If consumable has premium bonus, null is returned)
                bonuses.slice(0, 3).every(bonus => bonus === 0) && // Check if consumable has no energy/motivation/health
                (bonuses.slice(3, 7).every(bonus => bonus === 0) || bonuses[8] === 0) && // Check if consumable has no xp/product/luck/money with duration
                (bonuses[11] === 0 || (bonuses[9] === 0 || item.obj.usebonus.length !== 2)) && // Check if consumable has no travel with uses only
                (item.obj.has_cooldown || [bonuses[12], bonuses[13], bonuses[14]].filter(b => b !== 0).length < 2) && // Check if consumable has less than 2 battle bonuses
                (item.obj.has_cooldown || bonuses.slice(15, 17).every(bonus => bonus < 50)) // No battle character skills
            //)
        ) {
            return;
        }

        consumable.setCount(item.count);
        consumable.setEnergy(bonuses[0]);
        consumable.setMotivation(bonuses[1]);
        consumable.setHealth(bonuses[2]);
        consumable.setXp(bonuses[3]);
        consumable.setProduct(bonuses[4]);
        consumable.setLuck(bonuses[5]);
        consumable.setMoney(bonuses[6]);
        consumable.setOther(bonuses[7]);
        consumable.setDuration(bonuses[8]);
        consumable.setUses(bonuses[9]);
        consumable.setTravel(bonuses[11]);
        consumable.setOffense(bonuses[12]);
        consumable.setDefense(bonuses[13]);
        consumable.setBattleDamage(bonuses[14]);
        consumable.setHiding(bonuses[15]);
        consumable.setTraps(bonuses[16]);

        if ((item.obj.bufftype && item.obj.bufftype !== 0) || bonuses[10] == null) {
            consumable.setSpecial(true);

            if (item.obj.bufftype === 'character') {
                consumable.setCharacter(true);
            } else if (item.obj.bufftype === 'items' && !item.obj.has_cooldown && bonuses.slice(12, 15).some(b => b !== 0)) {
                consumable.setBattleItem(true);
            }
        }

        Maco.allConsumables.push(consumable);
    };
    Maco.removeConsumable = function(item) {
        const index = (item instanceof ConsumablePrototype)
            ? Maco.allConsumables.findIndex(c => c.id === item.id)
            : Maco.allConsumables.findIndex(c => c.id === item);

        if (index !== -1 && Maco.allConsumables[index].count > 0) {
            Maco.allConsumables[index].count--;
        }
    };
    Maco.parseConsumableBonuses = function(bonuses) {
        let result = Array(17).fill(0);
        const normalizedBonuses = bonuses.map(normalizeStr);

        for (const bonus of normalizedBonuses) {
            let type = -1;

            for (const { key, type: mappedType } of Maco.bonusTypeMap) {
                if (bonus.includes(key)) {
                    type = mappedType;
                    break;
                }
            }

            if (type !== -1) result[type] = extractNumberFromString(bonus);
        }

        return result;
    };
    Maco.loadAllConsumablesSelection = function() {
        if (Maco.consumablesSelection.length === 0) {
            Maco.defaultConsumablesSelection();
        } else {
            const selectedConsumablesMap = {};
            Maco.consumablesSelection.forEach(consumable => {
                selectedConsumablesMap[consumable.id] = consumable.selected;
            });
            Maco.allConsumables.forEach(consumable => {
                const isSelected = selectedConsumablesMap[consumable.id];
                if (isSelected != undefined) {
                    consumable.setSelected(isSelected);
                } else {
                    consumable.setSelected([52871000].includes(consumable.id) ? true : !consumable.hasSpecialBonus); // Keep bottle plug (52871000) selected by default
                }
            });
        }
    };
    Maco.saveConsumableSelection = function(id, selected) {
        const index = Maco.consumablesSelection.findIndex(consumable => consumable.id === id);
        if (index !== -1) {
            Maco.consumablesSelection[index].selected = selected;
        } else {
            Maco.consumablesSelection.push({ id: id, selected: selected });
        }
    };
    Maco.changeConsumableSelection = function(id, selected) {
        const index = Maco.allConsumables.findIndex(consumable => consumable.id === id);
        if (index !== -1) {
            Maco.allConsumables[index].setSelected(selected);
            Maco.saveConsumableSelection(id, selected);
        }
    };
    Maco.changeSelectionAllConsumables = function(selected) {
        for (let i = 0; i < Maco.allConsumables.length; i++) {
            Maco.allConsumables[i].setSelected(selected);
            Maco.saveConsumableSelection(Maco.allConsumables[i].id, selected);
        }
    };
    Maco.defaultConsumablesSelection = function() {
        for (let i = 0; i < Maco.allConsumables.length; i++) {
            let consumable = Maco.allConsumables[i];
            const shouldSelect = [52871000].includes(consumable.id) ? true : !consumable.hasSpecialBonus; // Keep bottle plug (52871000) selected by default

            consumable.setSelected(shouldSelect);
            Maco.saveConsumableSelection(consumable.id, shouldSelect);
        }
    };
    Maco.deselectConsumablesWithBuffs = function() {
        for (let i = 0; i < Maco.allConsumables.length; i++) {
            if (Maco.allConsumables[i].hasSpecialBonus) {
                Maco.allConsumables[i].setSelected(false);
                Maco.saveConsumableSelection(Maco.allConsumables[i].id, false);
            }
        }
    };
    Maco.filterConsumables = function(energy, motivation, health, buffs) {
        var result = [];
        for (let i = 0; i < Maco.allConsumables.length; i++) {
            if (energy && Maco.allConsumables[i].energy === 0) {
                continue;
            }
            if (motivation && Maco.allConsumables[i].motivation === 0) {
                continue;
            }
            if (health && Maco.allConsumables[i].health === 0) {
                continue;
            }
            if (buffs && !Maco.allConsumables[i].hasSpecialBonus) {
                continue;
            }
            result.push(Maco.allConsumables[i]);
        }
        return result;
    };
    Maco.countSetBits = function(number) {
        let count = 0;
        while (number > 0) {
            count += number & 1;
            number >>= 1;
        }
        return count;
    };
    Maco.heldKarpSymmetric = function(distances, startJob) {
        const n = distances.length;
        const memo = Array(1 << n).fill().map(() => Array(n).fill({ cost: Infinity, path: [] }));
        memo[1 << startJob][startJob] = { cost: 0, path: [startJob] };

        for (let subsetSize = 2; subsetSize <= n; subsetSize++) {
            for (let subset = 0; subset < (1 << n); subset++) {
                if (Maco.countSetBits(subset) === subsetSize && (subset & (1 << startJob))) {
                    for (let end = 0; end < n; end++) {
                        if ((subset & (1 << end)) !== 0) {
                            for (let prevEnd = 0; prevEnd < n; prevEnd++) {
                                if (prevEnd !== end && (subset & (1 << prevEnd)) !== 0) {
                                    const newCost = memo[subset ^ (1 << end)][prevEnd].cost + distances[prevEnd][end];
                                    if (newCost < memo[subset][end].cost) {
                                        memo[subset][end] = { cost: newCost, path: memo[subset ^ (1 << end)][prevEnd].path.concat([end]) }
                                    }
                                }
                            }
                        }
                    }
                }
            }
        }
        let minCost = Infinity;
        let minPath = [];
        for (let end = 0; end < n; end++) {
            if (end !== startJob && memo[(1 << n) - 1][end].cost < minCost) {
                minCost = memo[(1 << n) - 1][end].cost;
                minPath = memo[(1 << n) - 1][end].path;
            }
        }
        return { cost: minCost, path: minPath }
    };
    Maco.getOptimalRoute = function(distanceMatrix) {
        const jobsCount = distanceMatrix.length;
        const routes = [];
        for (let startJob = 0; startJob < jobsCount; startJob++) {
            const { cost, path } = Maco.heldKarpSymmetric(distanceMatrix, startJob);
            routes.push({ cost, path });
        }
        return routes.reduce(function(prev, curr) {
            return prev.cost < curr.cost ? prev : curr;
        })
    };
    Maco.createDistanceMatrix = function() {
        var distances = new Array(Maco.addedJobs.length);
        for (let i = 0; i < distances.length; i++) {
            distances[i] = new Array(Maco.addedJobs.length);
        }
        for (let i = 0; i < distances.length; i++) {
            for (let j = i; j < distances[i].length; j++) {
                if (i == j) {
                    distances[i][j] = distances[j][i] = Number.MAX_SAFE_INTEGER;
                    continue;
                }
                distances[i][j] = distances[j][i] = GameMap.calcWayTime({x:Maco.addedJobs[i].x,y:Maco.addedJobs[i].y},{x:Maco.addedJobs[j].x,y:Maco.addedJobs[j].y});
            }
        }
        return distances;
    };
    Maco.setEntryPoint = function(jobs) {
        if (jobs.length === 0) return;
        let minDistanceIndex = 0;
        let minDistance = jobs[0].distance;
        for (let i = 1; i < jobs.length; i++) {
            if (jobs[i].distance < minDistance) {
                minDistance = jobs[i].distance;
                minDistanceIndex = i;
            }
        }
        Maco.currentJob.jobIdx = minDistanceIndex;
    };
    Maco.calculateJobDistances = function() {
        for (let i = 0; i < Maco.addedJobs.length; i++) {
            Maco.addedJobs[i].calculateDistance();
        }
    };
    Maco.makeRoute = function() {
        if (Maco.addedJobs.length === 1) {
            Maco.addedJobsOld = [...Maco.addedJobs];
            Maco.addedJobs = [Maco.addedJobs[0]];
            return;
        }

        Maco.calculateJobDistances();

        if (Maco.addedJobsChanged()) {
            const runningJob = Maco.addedJobs[Maco.currentJob.jobIdx];
            const distanceMatrix = Maco.createDistanceMatrix();
            const optimalRoute = Maco.getOptimalRoute(distanceMatrix);
            const addedJobsOrder = [];
            for (const index of optimalRoute.path) {
                addedJobsOrder.push(Maco.addedJobs.at(index));
            }
            Maco.addedJobs = addedJobsOrder;
            Maco.addedJobsOld = [...addedJobsOrder];
            Maco.wayTimes = null;
            Maco.addedJobsHasChanged = true;
            if (Maco.isRunning) {
                Maco.currentJob.jobIdx = Maco.addedJobs.findIndex(job => job.id === runningJob.id && job.x === runningJob.x && job.y === runningJob.y);
                Maco.currentJob.direction = !Maco.currentJob.direction;
            } else {
                Maco.currentJob = { jobIdx: 0, direction: true }
            }
        }

        if (!Maco.isRunning) {
            Maco.setEntryPoint(Maco.addedJobs);
        }
    };
    Maco.createRoute = function() {
        Maco.calculateJobDistances();
        if (!Maco.addedJobsChanged()) {
            if (!walkToJob_running) {
                Maco.setEntryPoint(Maco.addedJobs);
            }
            return;
        }
        const runningJob = Maco.addedJobs[Maco.currentJob.jobIdx];
        let closestJobIndex = 0;
        let closestDistance = Maco.addedJobs[0].distance;
        let route = [];
        const distances = Maco.createDistanceMatrix();
        var getClosestJob = function(index, route, distances) {
            var closestDistance = Number.MAX_SAFE_INTEGER;
            var closestIndex = -1;
            for (let i = 0; i < distances.length; i++) {
                if (index === i || route.includes(i)) {
                    continue;
                }
                if (distances[i][index] < closestDistance) {
                    closestDistance = distances[i][index];
                    closestIndex = i;
                }
            }
            return closestIndex;
        };
        for (let i = 1; i < Maco.addedJobs.length; i++) {
            if (Maco.addedJobs[i].distance < closestDistance) {
                closestDistance = Maco.addedJobs[i].distance;
                closestJobIndex = i;
            }
        }
        route.push(closestJobIndex);
        while (route.length < Maco.addedJobs.length) {
            let closestJob = getClosestJob(route[route.length-1], route, distances);
            route.push(closestJob);
        }
        var addedJobsOrder = [];
        for (let i = 0; i < route.length; i++) {
            addedJobsOrder.push(Maco.addedJobs[route[i]]);
        }
        Maco.addedJobs = addedJobsOrder;
        Maco.addedJobsOld = [...addedJobsOrder];
        Maco.wayTimes = null;
        Maco.addedJobsHasChanged = true;
        if (Maco.isRunning) {
            Maco.currentJob.jobIdx = Maco.addedJobs.findIndex(job => job.id === runningJob.id && job.x === runningJob.x && job.y === runningJob.y);
        } else {
            Maco.currentJob = { jobIdx: 0, direction: true }
        }
    };
    Maco.addedJobsChanged = function(array1 = Maco.addedJobs, array2 = Maco.addedJobsOld) {
        if (array1.length !== array2.length) {
            return true;
        }
        for (let i = 0; i < array1.length; i++) {
            if (array1[i].id !== array2[i].id || array1[i].x !== array2[i].x || array1[i].y !== array2[i].y) {
                return true;
            }
        }
        return false;
    };
    Maco.equipSet = async function(set) {
        let equipError = false;
        let finished = false;

        const specialSets = new Map([
            [-2, { ride: 100 }],
            [-3, { health: 100 }],
        ]);

        if (specialSets.has(set)) {
            finished = await Maco.equipBestCustomGear(specialSets.get(set));
            if (finished) Maco.maxHealthForSet.set(set, Character.maxHealth);

            return {equipped: finished, error: equipError};
        }

        const wardrobeSet = Maco.wardrobe.get(set);
        if (wardrobeSet) {
            const missingItems = await Maco.equipGear(wardrobeSet.items);
            if (missingItems.length > 0) {
                Maco.showAlert(`Wardrobe (TW Calc) <b>${wardrobeSet.name}</b> set has saved missing item!`);
            }
            finished = Maco.isGearEquiped(wardrobeSet.items);
            if (finished) Maco.maxHealthForSet.set(set, Character.maxHealth);

            return {equipped: finished, error: equipError};
        }

        if (set <= -1) return {equipped: false, error: false};

        if (!Maco.sets.has(set)) {
            Maco.showAlert(Maco.alertTranslations[Maco.translationLang].alert_2(set));
            Maco.showNotification("The West - Set Error", "Trying to equip invalid set..", "error");
            const backupSet = (set == Maco.travelSet) ? -2 : set == Maco.healthSet ? -3 : set;
            if (specialSets.has(backupSet)) {
                finished = await Maco.equipBestCustomGear(specialSets.get(backupSet));
                if (finished) Maco.maxHealthForSet.set(set, Character.maxHealth);
            }

            return {equipped: finished, error: equipError};
        }

        let startTime = performance.now();
        const setItems = ["head", "neck", "body", "right_arm", "left_arm", "belt", "foot", "animal", "yield", "pants"]
            .map(key => Maco.sets.get(set)[key])
            .filter(value => value != null);

        function handleEquipError(msg) {
            equipError = true;
            return EventHandler.ONE_TIME_EVENT;
        }

        EventHandler.listen('equip_error', handleEquipError);
        EquipManager.switchEquip(Maco.sets.get(set).equip_manager_id);

        while ((performance.now() - startTime) < FUNCTION_TIMEOUT) {
            await wait(interval_short);
            finished = Maco.isGearEquiped(setItems);
            if (finished || equipError || !Maco.isRunning) break;
        }

        EventHandler.unlisten('equip_error', handleEquipError);

        if (finished) {
            Maco.maxHealthForSet.set(set, Character.maxHealth);
            removeUiElement("ui_inv_changed");
        } else if (Array.from(Maco.sets.keys()).indexOf(set) > 2 && !Premium.hasBonus('automation')) {
            Maco.showAlert(Maco.alertTranslations[Maco.translationLang].alert_3);
            Maco.showNotification("The West - Problem in game", "Cannot equip set.. 'Automation' premium ended.", "error");
        } else if (!Maco.equipError && Maco.isRunning) {
            if (!await Maco.checkInternetConnection()) {
                if (await Maco.waitForInternetConnection()) {
                    return await Maco.equipSet(set);
                }
            } else {
                Maco.loadSets(function(){});
            }
        }

        return {equipped: finished, error: equipError};
    };
    Maco.isWearing = function(itemId) {
        const item = ItemManager.get(itemId);
        if (!item || !Wear.wear[item.type]) return false;

        const wornItemId = Wear.wear[item.type].obj.item_id;
        if (wornItemId == itemId) return true;

        // Check if the last digit of wornItemId is greater than itemId's last digit
        const baseItemId = Math.floor(itemId / 10); // Remove the last digit
        const baseWornItemId = Math.floor(wornItemId / 10);

        if (baseItemId === baseWornItemId) {
            return (wornItemId % 10) >= (itemId % 10); // Get last digit representing item level
        }

        return false;
    };
    Maco.isGearEquiped = function(items, uncarryKeys = []) {
        for (let i = 0; i < items.length; i++) {
            if (!Maco.isWearing(items[i])) return false;
        }
        for (let key of uncarryKeys) {
            if (Wear.wear[key] != undefined) return false;
        }
        return true;
    };
    Maco.getBestGear = function(jobId, jobSkills) { 
        const jobIndex = JobsModel.Jobs.findIndex(job => job.id == jobId);
        if (jobIndex === -1 && !jobSkills) {
            return null;
        }
        jobSkills = jobSkills || JobsModel.Jobs[jobIndex]?.get('skills');
        const result = west.item.Calculator.getBestSet(jobSkills, jobId);
        return result && result.getItems() || [];
    };
    Maco.filterBestGear = function(items) {
        let invItems = Bag.getItemsByItemIds(items), result = [], invItem, wearItem;

        for (let i = 0; i < invItems.length; i++) {
            invItem = invItems[i];
            wearItem = Wear.get(invItem.getType());
            if (!wearItem || (wearItem && (wearItem.getItemBaseId() !== invItem.getItemBaseId() || wearItem.getItemLevel() < invItem.getItemLevel()))) {
                result.push(invItem.obj.item_id);
            }
        }

        return result;
    };
    Maco.equipBestCustomGear = async function(jobSkills, jobId = null) {
        const bestGear = Maco.filterBestGear(Maco.getBestGear(jobId, jobSkills));
        let finished = false;
        const startTime = performance.now();

        for (let i = 0; i < bestGear.length; i++) {
            if (!Maco.isWearing(bestGear[i])) {
                const item = Bag.getItemByItemId(bestGear[i]);
                if (item != undefined) {
                    Wear.carry(item);
                }
            }
        }

        while ((performance.now() - startTime) < EQUIP_TIMEOUT) {
            finished = Maco.isGearEquiped(bestGear);
            if (finished) break;
            await wait(interval_long);
        }

        return Promise.resolve(finished);
    };
    Maco.wearHandleClothChange = function(data, item, change, successCallback, finishCallback) {
        WearSet.setUpItems(data.wearSets);
        WearSet.setWorkPointBonus(data.workPointBonus);
        CharacterSkills.updateAllBonuspoints(data.bonus.allBonuspoints);
        Character.setSpeed(data.speed);
        Character.calcMaxHealth();
        EventHandler.signal('health', [Character.health, Character.maxHealth]);

        if (data.error) {
            new UserMessage(data.message || data.error, UserMessage.TYPE_ERROR).show();
        } else {
            Bag.updateChanges(data.changes, "wear");
            if (successCallback) successCallback.call();
            if (item.obj.type == 'right_arm') {
                EventHandler.signal('character_weapon_changed', [ItemManager.get(item.obj.item_id)]);
            }
            EventHandler.signal('wear_changed', [change]);
            Wear.renderWear();
        }

        if (finishCallback) finishCallback();
    };
    Maco.wearCarry = function(item, callback) {
        var newItem = item.obj;
        var change = {
            added: [newItem],
            removed: [Wear.wear[newItem.type] && Wear.wear[newItem.type].obj] || []
        };

        Ajax.remoteCall('inventory', 'carry', {
            item_id: item.obj.item_id,
            last_inv_id: Bag.getLastInvId()
        }, function(json) {
            Maco.wearHandleClothChange(json, item, change, function() {
                Wear.add(item.obj.item_id);
            }, function() {
                if (callback) callback();
            });
        });
    };
    Maco.equipGear = async function(gear, uncarryKeys = []) {
        const missingItems = [];
        const promises = [];

        for (const itemId of gear) {
            if (!Maco.isWearing(itemId)) {
                const item = Bag.getItemByItemId(itemId);
                if (item) {
                    const wearPromise = new Promise((resolve) => { // Create a promise for each wearCarry call
                        const timeoutId = setTimeout(() => {
                            console.warn("%cMaco.wearCarry not finished within timeout, continuing execution...", "color: cyan");
                            resolve();
                        }, EQUIP_TIMEOUT);

                        Maco.wearCarry(item, () => {
                            clearTimeout(timeoutId);
                            resolve();
                        });
                    });

                    promises.push(wearPromise);
                } else {
                    missingItems.push(" " + ItemManager.get(itemId).name);
                }
            }
        }

        await Promise.all(promises); // Wait for all wearCarry calls to complete before continuing
        //Wear.renderWear();

        for (let i = 0; i < uncarryKeys.length; i++) {
            if (Wear.wear[uncarryKeys[i]] != undefined)
                Wear.uncarry(uncarryKeys[i]);
        }

        return missingItems;
    };
    Maco.equipBestGear = async function(jobid, walkingToJob = false, retry = 1) {
        if (equipBestGear_running) {
            console.warn("%cDouble-call warning! Async function 'Maco.equipBestGear' is already in progress.. return..", 'color: cyan');
            return Promise.resolve(true);
        }
        equipBestGear_running = true;

        try {
            let jobGear;
            let bestGear;
            let uncarryKeys = [];

            function checkFarmingJobs() { // Equip no gear by default when farming jobs that unlocks at level less than 10 to earn the least possible XP.
                const farmingJobs = [17,23,18,5,6,12,9,4,8,2,92,3,11,7,1,93,13,14,15,20,22,10]; // job id
                for (let jobId of farmingJobs) {
                    const jobLevel = JobsModel.getById(jobId).jobObj.level;
                    if (jobid === jobId && Character.level >= jobLevel) {
                        for (let level = jobLevel; level <= 9; level++) {
                            if (!Maco.isGearSaved(jobId, level)) {
                                Maco.saveCurrentGear(jobId, level, true);
                            }
                        }
                        return true;
                    }
                }
                return false; // No match
            }

            if (Maco.farmingAssistant.enabled && [1, 2].includes(Maco.addedJobs.length)) {
                jobGear = Maco.jobsFarmingGear.find(item => item.jobid === jobid);
                if (!jobGear && Maco.lastResult[Maco.currentJob.jobIdx] > 0 && Character.level <= 9 && checkFarmingJobs()) {
                    jobGear = Maco.jobsFarmingGear.find(item => item.jobid === jobid); // Equip no gear from checkFarmingJobs() for certain jobs when under level 10.
                }
                if (jobGear) {
                    if (Character.level <= 9 && Maco.lastResult[Maco.currentJob.jobIdx] > 0) {
                        bestGear = jobGear[`level_${Character.level}`]?.gear || jobGear[`level_0`]?.gear;
                        uncarryKeys = jobGear[`level_${Character.level}`]?.uncarry || jobGear[`level_0`]?.uncarry || [];
                    } else {
                        bestGear = jobGear[`level_0`]?.gear;
                        uncarryKeys = jobGear[`level_0`]?.uncarry || [];
                    }
                }
            }

            if (!jobGear || (!bestGear && !uncarryKeys.length)) {
                jobGear = Maco.jobsBestGear.find(item => item.jobid === jobid);
                bestGear = jobGear ? jobGear[`level_0`]?.gear : undefined;
                uncarryKeys = jobGear ? jobGear[`level_0`]?.uncarry || [] : [];
            }

            if (!bestGear) {
                bestGear = Maco.getBestGear(jobid);
                if (bestGear && bestGear.length) {
                    Maco.jobsBestGear.push({ jobid: jobid, [`level_0`]: { gear: bestGear, uncarry: [] } });
                } else {
                    return Promise.resolve(true);
                }
            }

            while (TaskQueue.queue.length > 0 && !walkingToJob) {
                await wait(interval_long);
                if (!Maco.isRunning) return Promise.resolve(true);
            }

            const missingItems = await Maco.equipGear(Maco.filterBestGear(bestGear), uncarryKeys); // Equip gear

            if (missingItems.length > 0) {
                let index = Maco.jobsBestGear.findIndex(item => item.jobid === jobid);
                if (index !== -1) Maco.jobsBestGear.splice(index, 1);
                index = Maco.jobsFarmingGear.findIndex(item => item.jobid === jobid);
                if (index !== -1) {
                    delete Maco.jobsFarmingGear[index].level_0;
                    Maco.refreshTab("addedJobs");
                    Maco.showAlert(Maco.alertTranslations[Maco.translationLang].alert_4(Maco.getJobName(jobid), missingItems));
                    if (Maco.jobsFarmingGear[index][`level_${Character.level}`]) {
                        Maco.showNotification("The West - Script has stopped", "Missing items.", "error");
                        Maco.handleButtonStopClick();
                        return Promise.resolve(false);
                    }
                }
                if (retry > 0 && Character.level > 9) {
                    equipBestGear_running = false;
                    return await Maco.equipBestGear(jobid, walkingToJob, retry - 1);
                }
            }

            const finished = Maco.isGearEquiped(bestGear, uncarryKeys);

            if (!finished && missingItems.length === 0 && Maco.isRunning) {
                if (!await Maco.checkInternetConnection()) {
                    if (await Maco.waitForInternetConnection()) {
                        equipBestGear_running = false;
                        return await Maco.equipBestGear(jobid, walkingToJob);
                    }
                } else if (retry > 0) {
                    console.warn(`%cBest gear not properly equipped.. '${Maco.getJobName(jobid)}' retry.. ` + timestamp(), 'color: cyan');
                    equipBestGear_running = false;
                    return await Maco.equipBestGear(jobid, walkingToJob, retry - 1);
                } else {
                    console.warn(`%cThere was problem equipping best gear for job: '${Maco.getJobName(jobid)}' - ` + timestamp(), "color: pink");
                }
            }

            return Promise.resolve(finished);

        } catch (e) {
            const msg = "Error in 'Maco.equipBestGear': ";
            console.error(msg, e.stack);
            const index = Maco.jobsBestGear.findIndex(item => item.jobid === jobid);

            if (index !== -1) {
                Maco.jobsBestGear.splice(index, 1);
            }

            if (retry > 0) {
                console.log("Retrying equipBestGear..");
                equipBestGear_running = false;
                return await Maco.equipBestGear(jobid, walkingToJob, retry - 1);
            }

            Maco.handleError(e, msg);
            return Promise.resolve(false);
        } finally {
            equipBestGear_running = false;
        }
    };
    Maco.saveCurrentGear = function(jobid, level = 0, saveNoGear = false) { 
        const keys = ["animal", "yield", "right_arm", "left_arm", "foot", "pants", "belt", "body", "neck", "head"];
        let gear = [];
        let uncarryKeys = [];

        for (let i = 0; i < keys.length; i++) {
            if (saveNoGear) {
                uncarryKeys.push(keys[i]);
            } else {
                if (Wear.wear[keys[i]] != undefined) {
                    gear.push(Wear.wear[keys[i]].obj.item_id);
                } else {
                    uncarryKeys.push(keys[i]);
                }
            }
        }

        // Check if the jobGear entry already exists in jobsFarmingGear
        let jobGear = Maco.jobsFarmingGear.find(item => item.jobid === jobid);
        if (jobGear) {
            jobGear[`level_${level}`] = { gear: gear, uncarry: uncarryKeys };
        } else {
            Maco.jobsFarmingGear.push({ jobid: jobid, [`level_${level}`]: { gear: gear, uncarry: uncarryKeys } });
        }

        // If it's level 0, also update the best gear logic
        if (level === 0) {
            const bestGearIndex = Maco.jobsBestGear.findIndex(item => item.jobid === jobid);
            if (bestGearIndex !== -1) {
                Maco.jobsBestGear[bestGearIndex][`level_${level}`] = { gear: gear, uncarry: uncarryKeys };
            } else {
                Maco.jobsBestGear.push({ jobid: jobid, [`level_${level}`]: { gear: gear, uncarry: uncarryKeys } });
            }
        }
    };
    Maco.deleteSavedGear = function(jobid, level = 0) {
        let deleted = false;
        const index = Maco.jobsFarmingGear.findIndex(item => item.jobid === jobid);

        if (index !== -1) {
            let jobGear = Maco.jobsFarmingGear[index];
            if (jobGear.hasOwnProperty(`level_${level}`)) {
                delete jobGear[`level_${level}`];
                deleted = true;
            }
            if (Object.keys(jobGear).length === 1) {
                Maco.jobsFarmingGear.splice(index, 1);
            }
        }

        if (level === 0) {
            const gearIndex = Maco.jobsBestGear.findIndex(item => item.jobid === jobid);
            if (gearIndex !== -1) {
                Maco.jobsBestGear.splice(gearIndex, 1);
                deleted = true;
            }
        }

        return deleted;
    };
    Maco.isGearSaved = function(jobid, level = 0) {
        let jobGear = Maco.jobsFarmingGear.find(item => item.jobid === jobid);

        if (jobGear && jobGear[`level_${level}`]) {
            let savedGear = jobGear[`level_${level}`];

            if (savedGear.gear.length > 0 || savedGear.uncarry.length > 0) {
                return true;
            }
        }

        return false;
    };
    Maco.exportFarmingGear = function(jobid) {
        let jobGear = Maco.jobsFarmingGear.find(item => item.jobid === jobid);

        if (jobGear) {
            let jobGearCopy = JSON.parse(JSON.stringify(jobGear)); // Create a copy of jobGear to modify without affecting the original

            // Add comments to the 'gear' items for export (ignore during import)
            Object.keys(jobGearCopy).forEach(key => {
                if (key.startsWith('level_')) {
                    let levelData = jobGearCopy[key];
                    if (levelData && levelData.gear && Array.isArray(levelData.gear)) {
                        levelData.gear.forEach((itemId, index) => {
                            let itemName = ItemManager.get(itemId).name;
                            levelData.gear[index] = `${itemId}, ${itemName}`; // Format as "itemId, (itemName)"
                        });
                    }
                }
            });

            // Convert jobGearCopy to formatted JSON string
            let jsonData = JSON.stringify(jobGearCopy, null, 2); // Indent with 2 spaces

            let blob = new Blob([jsonData], { type: 'text/plain' }); // Create a Blob containing the JSON data

            // Create a link element to trigger the download
            let link = document.createElement('a');
            link.href = URL.createObjectURL(blob);
            link.download = `${Maco.getJobName(jobid)}.txt`; // Save as .txt file
            link.style.display = 'none';
            document.body.appendChild(link);

            link.click(); // Click the link to trigger download

            // Clean up
            document.body.removeChild(link);
            setTimeout(() => URL.revokeObjectURL(link.href), 0); // Use a small delay to ensure download starts
        } else {
            new UserMessage("Nothing is saved for this job!", UserMessage.TYPE_ERROR).show();
            //console.log(`Farming gear data not found for: ${Maco.getJobName(jobid)}`);
        }
    };
    Maco.importFarmingGear = function() {
        function convertImportedData(data) {
            let newData = JSON.parse(JSON.stringify(data)); // Create a deep copy of the imported data to modify without affecting the original

            // Remove comments from 'gear' items and format back to original structure
            Object.keys(newData).forEach(key => {
                if (key.startsWith('level_')) {
                    let levelData = newData[key];
                    if (levelData && levelData.gear && Array.isArray(levelData.gear)) {
                        levelData.gear.forEach((gearItem, index) => {
                            if (typeof gearItem === 'string') {
                                let parts = gearItem.split(', ');
                                if (parts.length === 2) {
                                    let itemId = parseInt(parts[0]);
                                    levelData.gear[index] = itemId;
                                }
                            }
                        });
                    }
                }
            });

            return newData;
        }

        return new Promise((resolve, reject) => {
            let input = document.createElement('input'); // Create an input element for file selection
            input.type = 'file';
            input.accept = '.json, .txt'; // Accept both JSON and TXT files

            input.onchange = function(event) { // Handle file selection
                let file = event.target.files[0];
                if (!file) {
                    reject(new Error('No file selected'));
                    return;
                }

                let reader = new FileReader(); // Read the file contents
                reader.onload = function(event) {
                    try {
                        let jsonData = event.target.result;
                        let importedData = JSON.parse(jsonData);

                        let existingIndex = Maco.jobsFarmingGear.findIndex(item => item.jobid === importedData.jobid);
                        if (existingIndex !== -1) {
                            Maco.jobsFarmingGear[existingIndex] = convertImportedData(importedData); // Update existing entry
                        } else {
                            Maco.jobsFarmingGear.push(convertImportedData(importedData)); // Add new entry
                        }

                        resolve(true);

                    } catch (e) {
                        console.error('Error parsing JSON file: ', e.stack);
                        reject(new Error('Error parsing JSON file'));
                    }
                };

                reader.readAsText(file);
            };

            input.click(); // Trigger file selection dialog
        });
    };
    Maco.checkMotivation = function(index, result, callback) {
        if (result.length === Maco.addedJobs.length && !Maco.addedJobsHasChanged) {
            Maco.lastResult = [...result];
            callback(result);
            return;
        }
        result = [];

        const processMotivation = (idx) => {
            if (!Maco.isRunning) return; // Stop if the process is no longer running.

            Maco.loadJobMotivation(idx, function(motivation) {
                if (!Maco.isRunning) return; // Stop if the process is no longer running.
                result.push(motivation);

                if (idx + 1 < Maco.addedJobs.length) { // Continue processing the next job.
                    processMotivation(idx + 1);
                } else { // All jobs processed, save result and invoke callback.
                    Maco.lastResult = [...result];
                    Maco.addedJobsHasChanged = false;
                    callback(result);
                }
            });
        };

        if (index < Maco.addedJobs.length) {
            processMotivation(index);
        } else { // Handle invalid index input.
            console.error(`Error in Maco.checkMotivation. Invalid index: ${index}. Index must be less than ${Maco.addedJobs.length}.`);
            callback([]);
        }
    };
    Maco.isMotivationAbove = function(result) {
        if (Maco.isStopMotivationZero()) return true;
        for (let i = 0; i < result.length; i++) {
            if (result[i] > Maco.addedJobs[i].stopMotivation) {
                return true;
            }
        }
        return false;
    };
    Maco.isMotivationAboveLow = function(result) {
        if (Maco.isStopMotivationZero()) return true;
        for (let i = 0; i < result.length; i++) {
            if (result[i] > Maco.addedJobs[i].stopMotivation + 5) {
                return true;
            }
        }
        return false;
    };
    Maco.jobsBelowMotivation = function(result) {
        if (!result) return 0;
        let count = 0;
        for (let i = 0; i < result.length; i++) {
            if (result[i] <= Maco.addedJobs[i].stopMotivation && Maco.addedJobs[i].stopMotivation > 0) {
                count++;
            }
        }
        return count;
    };
    Maco.averageMissingMotivation = function(result) {
        if (!result) return 0;
        const event = Maco.getEventBuff(Maco.searchKeys[Maco.language]?.motivationEventBuff);
        let motivation = 0;
        for (let i = 0; i < result.length; i++) {
            motivation += ((100 + event) - result[i]);
        }
        return motivation / result.length;
    };
    Maco.totalMotivationLeft = function(result) {
        if (result.length < Maco.addedJobs.length) return 0;
        let motivation = 0;

        for (let i = 0; i < Maco.addedJobs.length; i++) {
            const currentResult = result[i];

            if (typeof currentResult === 'number' && !isNaN(currentResult)) {
                motivation += (currentResult - Maco.addedJobs[i].stopMotivation);
            }
        }

        return motivation;
    };
    Maco.isMotivationRequired = function() {
        return Maco.settings.addMotivation && !Maco.isStopMotivationZero();
    };
    Maco.isStopMotivationZero = function() {
        for (let i = 0; i < Maco.addedJobs.length; i++) {
            if (Maco.addedJobs[i].stopMotivation <= 0) {
                return true;
            }
        }
        return false;
    };
    Maco.isHealthBelowLimit = function(healthStopValue = Maco.settings.healthStopValue, healthStopPercent = Maco.settings.healthStopPercent) {
        return (healthStopPercent >= ((Character.health / Character.maxHealth) * 100) && healthStopValue >= Character.health)
    };
    Maco.calcHealthRefill = async function(setInUse, fastCalc = false) {
        if (!Maco.sets.has(setInUse) && !Maco.wardrobe.has(setInUse) && !Maco.maxHealthForSet.has(setInUse))
            return 0;

        if (fastCalc && (!Maco.maxHealthForSet.has(setInUse) || !Maco.maxHealthForSet.has(Maco.healthSet)))
            return 0;

        let setInUseEquipped = true,
            healthSetEquipped = true;

        if (!Maco.maxHealthForSet.has(setInUse)) {
            setInUseEquipped = (await Maco.equipSet(setInUse)).equipped;
            await wait(interval_long);
        }

        if (!Maco.maxHealthForSet.has(Maco.healthSet))
            healthSetEquipped = (await Maco.equipSet(Maco.healthSet)).equipped;

        if (!setInUseEquipped || !healthSetEquipped)
            return 0;

        const healthMissing = Maco.maxHealthForSet.get(setInUse) - Character.health;
        return Math.round((healthMissing / Maco.maxHealthForSet.get(Maco.healthSet)) * 100);
    };
    Maco.useItemLoop = async function(toUse, amount = 0, delay) {
        let item;

        if (typeof toUse === 'object') {
            item = toUse;
        } else if (typeof toUse === 'number') {
            item = Bag.getItemByItemId(toUse);
        } else if (typeof toUse === 'string') {
            const itemArr = Maco.BagSearch(toUse);
            if (!itemArr || itemArr.length !== 1) {
                new UserMessage("Item name is not accurate or not found!", UserMessage.TYPE_ERROR).show();
                return;
            }
            const foundItem = itemArr[0].obj;
            if (foundItem.usetype === 'none' || foundItem.has_cooldown) {
                new UserMessage("Invalid item! Cannot use this item.", UserMessage.TYPE_ERROR).show();
                return;
            }
            item = itemArr[0];
        } else {
            return;
        }

        amount = Math.min(amount, item.count) || item.count;

        for (let i = 0; i < amount; i++) {
            try {
                ItemUse.doIt(item.obj.item_id);
                await wait(delay || 1000);
                if (Maco.invalidSession || document.querySelector('.critical-error')) {
                    break;
                }
                Maco.removeConfirmDialog();
            } catch (error) {
                console.error(`Error using item '${item.obj.name}': `, error);
                break;
            }
        }
    };
    Maco.getEventBuff = function(buffName) {
        if (buffName == undefined) return 0;
        const buffs = CharacterSkills.buffs;

        function cleanDescription(desc) {
            return desc.replace(/[+%0-9]/g, '').trim();
        }

        for (let key in buffs) {
            if (key.startsWith('event_')) {
                const description = buffs[key].description.find(desc => compareStrings(cleanDescription(desc), buffName, 0.85));
                return description ? extractNumberFromString(description) : 0;
            }
        }

        return 0;
    };
    Maco.loadActiveEventItemId = function() {
        let ids = [];

        const eventMapping = {
            'Hearts': [2558000, 2557000],
            'Easter': [2698000],
            'Independence': [51483000],
            'Octoberfest': [50691000],
            'DayOfDead': [2666000, 2665000]
        };

        for (let eventKey in eventMapping) {
            if ($(`.custom_unit_counter.${eventKey}`).length > 0) {
                ids = eventMapping[eventKey];
                break;
            }
        }

        return ids;
    };
    Maco.startSpecialConsumableInterval = function() {
        const executeConsumables = () => {
            const nuggetId = [2482000]; // magic nugget bag
            const consumableIds = [...nuggetId, ...Maco.loadActiveEventItemId()]; // Combine all IDs (flatten into one array)

            let usedConsumables = [];

            consumableIds.forEach(id => {
                if (Maco.useSpecialConsumable(id)) {
                    usedConsumables.push(id);
                }
            });

            setTimeout(() => {
                if (usedConsumables.length > 0) {
                    const cooldowns = usedConsumables.map(id => Maco.getConsumeCooldown(id) * 1000 || 3e5);
                    const minCooldown = Math.min(...cooldowns); // Get the shortest cooldown
                    setTimeout(executeConsumables, minCooldown);
                }
            }, timeout_regular); // Delay to ensure ItemUse.doIt(id) is finished and cooldowns updated
        };

        executeConsumables();
    };
    Maco.useSpecialConsumable = function(id) {
        if (id != null && Bag.getItemByItemId(id)) {
            if (Maco.canUseConsume(id) && Maco.currentState !== 5) {
                Maco.itemUse(id, ItemManager.get(id).name.trim());
            }
            return true;
        }
        return false;
    };
    Maco.getConsumeCooldown = function(itemId = 0) {
        if (itemId === 0 && Maco.allConsumables.length > 0) {
            const foundItem = Maco.allConsumables.find(item => item.energy !== 0 || item.motivation !== 0 || item.health !== 0);
            if (foundItem) {
                itemId = foundItem.id;
            } else {
                return 0;
            }
        }
        const item = Bag.getItemByItemId(itemId);
        if (item && BuffList.cooldowns[itemId] != undefined) {
            item.showCooldown();
            return Math.max((BuffList.cooldowns[itemId].time - new ServerDate().getTime()) / 1000, 0); // in seconds
        }
        return 0;
    };
    Maco.canUseConsume = function(itemId) {
        const item = Bag.getItemByItemId(itemId);
        if (item) {
            item.showCooldown();
            if ((BuffList.cooldowns[itemId] != undefined && BuffList.cooldowns[itemId].time > new ServerDate().getTime()) || !navigator.onLine) {
                return false;
            }
            return true;
        }
        return false;
    };
    Maco.canAddBuff = function(type) {
        if ($(`[id^="buff_div_${type}"]`).length > 0) {
            return false;
        }
        return CharacterSkills.buffs[type] == null;
    };
    Maco.tryUseBuff = function() {
        const calculateEnergyMissing = () => 100 - (Character.energy / Character.maxEnergy) * 100;
        let toAdd =
            Maco.settings.addXpBuff ? 'xp' :
            Maco.settings.addProductBuff ? 'product' :
            Maco.settings.addMoneyBuff ? 'money' :
            Maco.settings.addLuckBuff ? 'luck' :
            '';
        const characterBuff = Maco.canAddBuff('character') && toAdd !== '';
        const travelBuff = Maco.canAddBuff('travel') && Maco.settings.addTravelBuff;

        if (!characterBuff && travelBuff) {
            toAdd = 'travel';
        } else if (toAdd === '' || (!characterBuff && !travelBuff)) {
            return;
        }

        let consumables = Maco.allConsumables.filter(c => c.selected && c[toAdd] > 0 && c.count > 0);
        if (consumables.length === 0 && characterBuff && travelBuff) {
            toAdd = 'travel';
            consumables = Maco.allConsumables.filter(c => c.selected && c[toAdd] > 0 && c.count > 0);
        }

        if (consumables.length === 0 || useBuff_running) {
            return;
        }
        consumables.sort((a, b) => b.duration - a.duration);
        consumables.sort((a, b) => b[toAdd] - a[toAdd]);

        const battleTimer = Maco.getCurrentBattleTimer() / 60;
        let index = null;
        let indexes = [];

        for (let i = 0; i < consumables.length; i++) {
            if ((toAdd === 'travel' && consumables[i].uses !== 0 && ((Maco.settings.addEnergyOptional) ? consumables[i].bonuses.length === 2 : true)) ||
                (consumables[i].duration !== 0 && toAdd !== 'travel'))
            {
                if ((Character.level <= 19 && consumables[i].other > 0 && Maco.lastResult[Maco.currentJob.jobIdx] > 0) ||
                    (
                        consumables[i].hasCooldown &&
                        (
                            (consumables[i].motivation <= 5 && Maco.isMotivationRequired() && Maco.totalMotivationLeft(Maco.lastResult) < (Maco.getConsumeCooldown(consumables[i].id) / 15) + 39) ||
                            ((consumables[i].energy * Character.maxEnergy / 100 + Character.energy) < Maco.getConsumeCooldown() / 15 - TaskQueue.queue.length + 39)
                        )
                    )
                ) {
                    continue;
                }

                if (toAdd !== 'travel' && Maco.settings.fortBattle.overwriteCharacterBonus && battleTimer > 0 &&
                    (consumables[i].duration * 60) - battleTimer > (consumables[i].duration * 60) * BATTLE_BUFF_OVERWRITE_TOLERANCE
                ) {
                    continue;
                }

                if (index == null) { // The first item that satisfy condition above.
                    index = i;
                }

                if (consumables[i].energy > 0 && (!Maco.settings.addEnergy || consumables[i].energy > calculateEnergyMissing() + ENERGY_WASTE_TOLERANCE)) {
                    continue;
                }

                indexes.push(i);
            }
        }

        if (indexes.length > 0) {
            // Find the index of the item with the most energy
            index = indexes.reduce((maxIndex, currentIndex) => {
                return consumables[currentIndex].energy > consumables[maxIndex]?.energy ? currentIndex : maxIndex;
            }, indexes[0]); // Start with the first index as the initial maxIndex
        }

        if (index != null) {
            Maco.useBuff(consumables[index]);
        }
    };
    Maco.useBuff = async function(itemToUse) {
        if (!itemToUse) return;
        if (useBuff_running) {
            console.warn("%cDouble-call warning! Async function 'Maco.useBuff' is already in progress.. return..", 'color: cyan');
            return;
        }
        useBuff_running = true;

        try {
            let waiting = false;
            const stateBefore = Maco.currentState;

            while (Maco.isRunning && !useConsumable_running) {
                if (Maco.canUseConsume(itemToUse.id)) {
                    Maco.itemUse(itemToUse.id, itemToUse.name.trim());
                    /*setTimeout(() => {
                        Maco.refreshTab("consumables");
                    }, 1000);*/
                    break;
                } else if (!waiting) {
                    waiting = true;
                    Maco.currentState = 2;
                }
                await wait(interval_long);
            }

            if (waiting && Maco.isRunning && Maco.currentState === 2 && !useConsumable_running) {
                Maco.currentState = stateBefore;
            }
        } catch (e) {
            const msg = "Exception occured in 'Maco.useBuff()': ";
            console.error(msg, e.stack);
            Maco.handleError(e, msg);
        } finally {
            useBuff_running = false;
        }
    };
    Maco.removeConfirmDialog = function() {
        if ($(".tw2gui_dialog_framefix").length > 0) {
            $(".tw2gui_dialog_framefix").remove();
            return;
        }

        const removeDialogTimeout = setTimeout(() => {
            clearInterval(removeDialogInterval);
        }, timeout_regular);

        const removeDialogInterval = setInterval(() => {
            const dialogs = $(".tw2gui_dialog_framefix");
            if (dialogs.length > 0) {
                dialogs.remove();
                clearInterval(removeDialogInterval);
                clearTimeout(removeDialogTimeout);
            }
        }, interval_short);
    };
    Maco.itemUse = function(item_id, item_name) {
        EventHandler.listen('item_used', function() {
            setTimeout(() => {
                Maco.removeConfirmDialog();
                Maco.removeConsumable(item_id);
                if (item_name) {
                    Maco.diagnostics.consumablesUsed.push(item_name);
                    Maco.refreshTab("consumables");
                }
            }, 0);
            return EventHandler.ONE_TIME_EVENT;
        });

        ItemUse.doIt(item_id);
    };
    Maco.useConsumable = async function(itemToUse, lowMotivationFlag = false, optionalEnergy = false, battleFlag = false, equipHealthSet = true) {
        if (useConsumable_running) {
            console.warn("%cDouble-call warning! Async function 'Maco.useConsumable' is already in progress.. return..", 'color: cyan');
            return false;
        }
        useConsumable_running = true;

        try {
            let waiting = null;
            const stateBefore = Maco.currentState;

            while (Maco.isRunning) {
                if (Maco.canUseConsume(itemToUse.id)) {
                    if (itemToUse.health !== 0 && !walkToJob_running && !runJob_running && ![7].includes(stateBefore) && equipHealthSet) {
                        const maxHealthJob = Maco.maxHealthForSet.get(Maco.addedJobs[Maco.currentJob.jobIdx].set);
                        const maxHealth = (battleFlag) ? Character.maxHealth : maxHealthJob || Character.maxHealth;
                        const healthMissing = ((maxHealth - Character.health) / maxHealth) * 100;
                        const isSetChangeOptimal = healthMissing > itemToUse.health;

                        if (battleFlag ? isSetChangeOptimal : ((!optionalEnergy && !lowMotivationFlag) || isSetChangeOptimal)) {
                            await Maco.equipSet(Maco.healthSet);
                        }
                    }
                    const itemName = battleFlag ? itemToUse.name.trim() + " (Battle)" : (Maco.isHealthBelowLimit() ? itemToUse.name + " (LOW HP)" : itemToUse.name);
                    Maco.itemUse(itemToUse.id, itemName);
                    break;
                } else if (!waiting) {
                    if (battleFlag && (Maco.getCurrentBattleTimer() - BATTLE_START_MARGIN / 2 < Maco.getConsumeCooldown(itemToUse.id))) {
                        break;
                    }
                    waiting = new Date();
                    Maco.currentState = 2;
                }

                await wait(interval_long);
            }

            await wait(interval_long); // To prevent race conditions (energy/cooldown game update)

            if (Maco.isRunning && !optionalEnergy && !lowMotivationFlag && !battleFlag) {
                if (waiting) {
                    Maco.stats.session.consumableWaitingTime += calculateElapsedSeconds(waiting);
                    Maco.addWaitingReason("Used before: <" + Maco.diagnostics.consumablesUsed.at(-2) + "> | Waited for: <" + Maco.diagnostics.consumablesUsed.at(-1) + ">");
                }
                Maco.updateRuntime();
                Maco.run();
            } else if (Maco.isRunning) {
                Maco.currentState = stateBefore;
            }

            //Maco.refreshTab("consumables");
            return true;
        } catch (e) {
            const msg = "Exception occured in 'Maco.useConsumable': ";
            console.error(msg, e.stack);
            Maco.handleError(e, msg);
            return false;
        } finally {
            useConsumable_running = false;
        }
    };
    function sortByHealthMissing(consumes, healthMissing) {
        return consumes.sort((a, b) => {
            const diffA = Math.abs(a.health - healthMissing);
            const diffB = Math.abs(b.health - healthMissing);
            if (diffA !== diffB) {
                return diffA - diffB;
            }
            return b.health - a.health; // If proximity is the same, sort by more health
        });
    };
    function equalValuesOnly(consumes, attribute) {
        // Find the index of the first item with a different value for the given attribute
        const index = consumes.findIndex((item, i, arr) => i > 0 && item[attribute] !== arr[0][attribute]);
        // Slice the array to keep only the items with the same value for the given attribute
        return index !== -1 ? consumes.slice(0, index) : consumes;
    };
    Maco.findProperConsumable = function(jobsBelowMotivation,energyMissing,healthMissing,averageMotivationMissing,consumables,lowMotivationFlag,optionalEnergy,battleFlag) {
        function betterEnergy(item1, item2) {
            const targetEnergy = Math.min(energyMissing, Maco.maxAllowedEnergy);
            const distanceItem1 = Math.abs(targetEnergy - item1.energy);
            const distanceItem2 = Math.abs(targetEnergy - item2.energy);
            return distanceItem1 - distanceItem2;
        }
        function betterMotivation(item1, item2) {
            const adjust = (dist) => dist > 0 ? dist * 3 : dist; // Consumables that have lower motivation than needed are deprioritized in the sorting
            const distanceItem1 = adjust(averageMotivationMissing - item1.motivation);
            const distanceItem2 = adjust(averageMotivationMissing - item2.motivation);
            return Math.abs(distanceItem1) - Math.abs(distanceItem2);
        }

        function findMotivationConsume(consumes) {
            consumes.sort(betterMotivation);
            const lowHealthFlag = Maco.hasLowHealth();
            const idealConsume = consumes.find(c =>
                (c.motivation >= averageMotivationMissing || Math.abs(averageMotivationMissing - c.motivation) <= 5) &&
                (c.energy <= energyMissing + ENERGY_WASTE_TOLERANCE && c.energy * Character.maxEnergy / 100 + Character.energy >= 39) &&
                (!lowHealthFlag || c.health > 0)
            );
            if (idealConsume) return idealConsume; //return sortByHealthMissing(equalValuesOnly(equalValuesOnly(idealConsumes, 'energy'), 'motivation'), healthMissing)[0];

            let filteredConsumes = consumes.filter(c => c.motivation > 0 && (c.energy <= energyMissing + ENERGY_WASTE_TOLERANCE || Character.energy < 26));
            if (filteredConsumes.length === 0) {
                filteredConsumes = consumes.filter(c => c.motivation > 0);
            }
            for (let i = 0; i < filteredConsumes.length; i++) {
                if (filteredConsumes[i].energy * Character.maxEnergy / 100 + Character.energy >= 39) {
                    return filteredConsumes[i];
                }
            }
            return filteredConsumes[0];
        }

        function findHealthConsume(consumes) {
            const filteredConsumes = consumes.filter(c => c.health > 0);
            if (filteredConsumes.length === 0) return null;
            if (battleFlag) return equalValuesOnly(sortByHealthMissing(filteredConsumes, healthMissing), 'health').sort((a, b) => a.energy - b.energy)[0];
            let slicedConsumes = sortByHealthMissing(equalValuesOnly(filteredConsumes, 'energy'), healthMissing);

            if (Maco.isMotivationRequired() && Maco.totalMotivationLeft(Maco.lastResult) < 39) {
                if (slicedConsumes.sort(betterMotivation)[0].motivation === 0) {
                    const idealConsumes = filteredConsumes.filter(c =>
                        c.motivation > 0 &&
                        c.energy <= energyMissing + ENERGY_WASTE_TOLERANCE &&
                        c.energy * Character.maxEnergy / 100 + Character.energy >= 39
                    );
                    slicedConsumes = idealConsumes.length > 0 ? idealConsumes.sort(betterMotivation) : slicedConsumes;
                }
            } else {
                slicedConsumes.sort((a, b) => (a.health === b.health) ? a.motivation - b.motivation : 0);
            }

            return slicedConsumes[0];
        }

        function findEnergyConsume(consumes) {
            const lowHealthFlag = Maco.hasLowHealth();
            let filteredConsumes = consumes.filter(c => c.energy > 0);

            if (optionalEnergy) {
                filteredConsumes = filteredConsumes.filter(c => {
                    const lowHealthCondition = lowHealthFlag ? c.health > 0 : true;
                    const allowedMotivationCondition = ((c.motivation === 0 || Maco.settings.allowMotivationOptional) || (Maco.isStopMotivationZero() && Maco.settings.addMotivation));
                    const minEnergyLimitCondition = ((c.energy / 100) * Character.maxEnergy) + Character.energy >= (39 - TaskQueue.queue.length);

                    return c.energy <= Math.min(Maco.settings.addEnergyOptionalMax, energyMissing) && 
                    (
                        (c.energy >= Maco.maxAllowedEnergy || (minEnergyLimitCondition && c.energy >= Maco.settings.addEnergyOptionalMin)) &&
                        lowHealthCondition && allowedMotivationCondition
                    );
                });
                if (filteredConsumes.length === 0) {
                    return null;
                } else if (filteredConsumes.length === 1) {
                    return filteredConsumes[0];
                }
            }

            const slicedConsumes = sortByHealthMissing(equalValuesOnly(filteredConsumes, 'energy'), healthMissing);
            if (Maco.isMotivationRequired() && Maco.totalMotivationLeft(Maco.lastResult) < 39) {
                slicedConsumes.sort(betterMotivation);
            } else {
                slicedConsumes.sort((a, b) => a.motivation - b.motivation);
            }
            return slicedConsumes[0];
        }


        if (consumables.length === 0) return null;
        if (Maco.settings.addEnergy && !battleFlag) {
            consumables.sort(betterEnergy);
        } else {
            consumables.sort((a, b) => a.energy - b.energy);
        }

        if (Maco.isHealthBelowLimit() || battleFlag) {
            return findHealthConsume(consumables);
        }
        if (jobsBelowMotivation >= Maco.addedJobs.length || lowMotivationFlag) {
            return findMotivationConsume(consumables);
        }
        if (consumables[0].energy > 0 && (optionalEnergy || Character.energy < Maco.energyCost)) {
            return findEnergyConsume(consumables);
        }

        return null;
    };
    Maco.hasLowHealth = function() {
        const maxJobHealth = Maco.maxHealthForSet.get(Maco.addedJobs[Maco.currentJob.jobIdx].set) || Character.maxHealth;
        const healthMissing = ((maxJobHealth - Character.health) / maxJobHealth) * 100;

        return 100 - healthMissing < Maco.settings.healthStopPercent * 1.5 || (healthMissing > 70 && Character.health < Maco.settings.healthStopValue * 1.9);
    };
    Maco.tryFindConsumable = function(jobsBelowMotivation, averageMotivationMissing, healthMissing, lowMotivationFlag, optionalEnergy, battleFlag) {
        const energyMissing = 100 - (Character.energy / Character.maxEnergy) * 100;
        const selectedConsumes = Maco.allConsumables.filter(c =>
            c.selected && c.count > 0 &&
            (!c.hasCharacterBonus || (Maco.canAddBuff('character') && c.uses !== 0))
        );

        return Maco.findProperConsumable(jobsBelowMotivation, energyMissing, healthMissing, averageMotivationMissing, selectedConsumes, lowMotivationFlag, optionalEnergy, battleFlag);
    };
    Maco.tryUseConsumable = async function(result, healthMissing = 0, lowMotivationFlag = false, optionalEnergy = false, battleFlag = false, equipHealthSet = true) {
        if (healthMissing === 0) healthMissing = await Maco.calcHealthRefill(Maco.jobSet, true);

        const jobsBelowMotivation = Maco.jobsBelowMotivation(result);
        const averageMotivationMissing = Maco.averageMissingMotivation(result);

        const itemToUse = Maco.tryFindConsumable(jobsBelowMotivation, averageMotivationMissing, healthMissing, lowMotivationFlag, optionalEnergy, battleFlag);

        if (!itemToUse) {
            return false;
        }

        if (optionalEnergy || lowMotivationFlag) {
            if (!Maco.canUseConsume(itemToUse.id)) {
                return false;
            }
            await Maco.useConsumable(itemToUse, lowMotivationFlag, optionalEnergy, battleFlag, equipHealthSet);
        } else {
            Maco.useConsumable(itemToUse, lowMotivationFlag, optionalEnergy, battleFlag, equipHealthSet);
        }

        return true;
    };
    Maco.cancelJobsPromise = function() {
        return new Promise(resolve => {
            if (TaskQueue.queue.length === 0) {
                resolve();
            } else {
                if (navigator.onLine && Object.keys(TaskQueue.toCancel).length === 0) {
                    TaskQueue.cancelAll();
                }
                setTimeout(() => {
                    Maco.cancelJobsPromise().then(resolve);
                }, timeout_regular);
            }
        });
    };
    Maco.cancelJobs = async function() {
        while (TaskQueue.queue.length > 0 && navigator.onLine) {
            TaskQueue.cancelAll();
            await waitForEvent('taskqueue-ready');
        }
    };
    Maco.updateRuntime = function() {
        Maco.stats.session.runTime += calculateElapsedSeconds(Maco.startTime);
        Maco.startTime = new Date();
        Maco.debouncedSaveAll(0);
    };
    Maco.updateStatistics = function(oldXp, oldMoney) {
        const xpDifference = Character.experience - oldXp;
        const moneyDifference = Character.money > oldMoney ? Character.money - oldMoney : 0;
        Maco.stats.session.xp += xpDifference;
        Maco.stats.total.xp += xpDifference;
        Maco.stats.session.money += moneyDifference;
        Maco.stats.total.money += moneyDifference;
        Maco.updateRuntime();
        Maco.refreshTab("stats");
    };
    Maco.canAddMissing = function(result) {
        if (!Maco.settings.addMotivation && !Maco.isMotivationAbove(result) && !Maco.isStopMotivationZero()) {
            Maco.showAlert(Maco.alertTranslations[Maco.translationLang].alert_5);
            return {canContinue: false, reason: "motivation"};
        }
        if (!Maco.settings.addEnergy && Character.energy === 0) {
            Maco.showAlert(Maco.alertTranslations[Maco.translationLang].alert_6);
            return {canContinue: false, reason: "energy"};
        }
        if (!Maco.settings.addHealth && Maco.isHealthBelowLimit()) {
            Maco.showAlert(Maco.alertTranslations[Maco.translationLang].alert_7);
            return {canContinue: false, reason: "health"};
        }
        return {canContinue: true};
    };
    Maco.considerUseConsumable = async function(result, healthMissing = 0) {
        const answer = Maco.canAddMissing(result);
        if (!answer.canContinue) {
            if (answer.reason === "motivation") {
                Maco.sleep({ dontWakeUp: true, message: answer.reason, flag: answer.reason });
            } else {
                Maco.sleep({ message: answer.reason, flag: answer.reason });
            }
        } else if (!await Maco.tryUseConsumable(result, healthMissing)) {
            const message = Maco.maxAllowedEnergy === 100 ? Maco.alertTranslations[Maco.translationLang].alert_8 : "";
            if (message) Maco.showAlert(message);
            Maco.sleep({ message: message, flag: (Maco.isHealthBelowLimit()) ? "health" : "" });
        }
    };
    Maco.run = function() {
        Maco.checkMotivation(0, [], function(result) {
            if (Maco.invalidSession) return;
            if (Maco.isMotivationAbove(result) && Character.energy > 0 && !Maco.isHealthBelowLimit()) {
                Maco.currentState = 1;
                Maco.prepareJobRun(Maco.currentJob.jobIdx, result);
            } else {
                Maco.considerUseConsumable(result);
            }
        });
    };
    Maco.swapSilverJob = function(index, swapToSilver = true) {
        let job = Maco.getClosetSilverJob(Maco.addedJobs[index].id, swapToSilver);
        if (job != null) {
            job.setStopMotivation(Maco.addedJobs[index].stopMotivation);
            job.setSet(Maco.addedJobs[index].set);
            Maco.addedJobs.splice(index, 1, job);
            return true;
        } else {
            return false;
        }
    };
    Maco.optionalEnergyAllowed = function() {
        return Maco.settings.addEnergy && Maco.settings.addEnergyOptional && (Character.level >= 9 || Maco.lastResult[Maco.currentJob.jobIdx] === 0);
    }
    Maco.prepareJobRun = function(index, _result = [], walkingToJob = false) {
        if (!Maco.isRunning) return;
        const energyMissing = (queue = 0) => 100 - ((Character.energy - queue) / Character.maxEnergy) * 100;
        const energyCondition = (minEnergyResult, queue = 0) => Maco.optionalEnergyAllowed() && energyMissing(queue) >= Maco.settings.addEnergyOptionalMin &&
                                                                Character.energy + Character.maxEnergy * (Maco.settings.addEnergyOptionalMax / 100) >= minEnergyResult;
        setTimeout(function() {
            Maco.loadJobMotivation(index, async function(motivation) {
                const addedJob = Maco.addedJobs[index];

                if ([1, 2].includes(Maco.addedJobs.length) && Maco.addedJobs.every(job => job.stopMotivation <= 0)) {
                    if ((Maco.lastResult[index] === 0 || Maco.lastResultFarming[index] === 0) && motivation > 81) {
                        if (Maco.addedJobs.length === 2) {
                            Maco.removeJob(addedJob.x, addedJob.y, addedJob.id);
                            Maco.debouncedSaveAll(0);
                            if (Maco.settings.autoReload) {
                                Maco.reload("Daily jobs reset. Farming job changed.");
                            } else {
                                Maco.lastResult = [];
                                Maco.prepareJobRun(Maco.currentJob.jobIdx);
                                return;
                            }
                        } else if (Maco.farmingAssistant.stopLevel) {
                            Maco.handleButtonStopClick();
                            return;
                        }
                    }
                    if (!addedJob.silver && (motivation <= 0 || (characterId !== 0 && Maco.farmingAssistant.enabled)) && !Maco.farmingAssistant.jobSwapped) {
                        Maco.farmingAssistant.jobSwapped = true;
                        Maco.swapSilverJob(index);
                        Maco.selectTab("addedJobs");
                    } else if (motivation > 0 && addedJob.silver && Character.level <= 19) {
                        Maco.farmingAssistant.jobSwapped = false;
                        Maco.swapSilverJob(index, false);
                        Maco.selectTab("addedJobs");
                    }
                }

                Maco.lastResult[index] = motivation;
                Maco.lastResultFarming = [...Maco.lastResult];

                if (Character.energy === 0 || Maco.isHealthBelowLimit()) {
                    if (Maco.canAttendBattle()) {
                        Maco.attendFortBattle();
                        return;
                    }
                    Maco.run();
                } else if (motivation <= addedJob.stopMotivation && addedJob.stopMotivation > 0) {
                    Maco.checkMotivation(0, _result, function(result) {
                        if (Maco.isMotivationAbove(result)) {
                            do {
                                Maco.changeJob();
                            } while (result[Maco.currentJob.jobIdx] <= Maco.addedJobs[Maco.currentJob.jobIdx].stopMotivation && Maco.addedJobs[Maco.currentJob.jobIdx].stopMotivation > 0)
                            Maco.debouncedSaveAll(0);
                            Maco.prepareJobRun(Maco.currentJob.jobIdx, result);
                            return;
                        } else {
                            Maco.considerUseConsumable(result);
                        }
                    });
                } else if (Maco.isDestinationReached(Maco.addedJobs[Maco.currentJob.jobIdx]) || walkingToJob) {
                    const inQueue = TaskQueue.queue.length;
                    const motivationLeft = motivation - addedJob.stopMotivation;
                    const maxJobs = Premium.hasBonus('automation') ? TaskQueue.limit.premium : TaskQueue.limit.normal;
                    const energyLimit = Math.min(39, Character.energy + (Maco.maxAllowedEnergy * 150) / 100); // Minimum energy/motivation needed (after consumable used) to work without waiting for cooldown.
                    let addEnergyAfterJobs = false;

                    if (!walkingToJob && Maco.canAttendBattle()) {
                        Maco.attendFortBattle();
                        return;
                    }

                    if (addedJob.stopMotivation <= 0) {
                        var numberOfJobs = Math.min(Character.energy, maxJobs);
                    } else {
                        var numberOfJobs = Math.min(Math.min(motivationLeft - inQueue, Character.energy), maxJobs);
                    }

                    if (Maco.getConsumeCooldown() === 0 && (Maco.totalMotivationLeft(Maco.lastResult) >= energyLimit || !Maco.isMotivationRequired())) {
                        if (energyCondition(energyLimit) && TaskQueue.queue.length === 0 && !walkingToJob) {
                            addEnergyAfterJobs = !await Maco.tryUseConsumable(Maco.lastResult, 0, false, true);
                        } else if (energyCondition(energyLimit, numberOfJobs)) {
                            addEnergyAfterJobs = true;
                        }
                    }

                    Maco.runJob(index, numberOfJobs, walkingToJob, addEnergyAfterJobs);
                } else {
                    while (TaskQueue.queue.length > 0 && Maco.isRunning) {
                        Maco.cancelSleep(true);
                        await wait(interval_long);
                    }

                    const equipped = (await Maco.equipSet(Maco.travelSet)).equipped;
                    (equipped) ? Maco.saveWayTimes() : new UserMessage("'Travel set' could not be equipped!", UserMessage.TYPE_ERROR).show();

                    if (Maco.canAttendBattle(equipped)) {
                        Maco.attendFortBattle();
                        return;
                    }

                    Maco.checkMotivation(0, _result, function(result) {
                        let canAddEnergy = false;
                        let lowMotivation = false;
                        const energyLimit = Math.min(39, Character.energy + (Maco.maxAllowedEnergy * 150) / 100);

                        if (motivation <= addedJob.stopMotivation + 5 && Maco.isMotivationRequired()){
                            if (Maco.isMotivationAboveLow(result)) {
                                do {
                                    Maco.changeJob();
                                } while (result[Maco.currentJob.jobIdx] <= Maco.addedJobs[Maco.currentJob.jobIdx].stopMotivation + 5 && Maco.addedJobs[Maco.currentJob.jobIdx].stopMotivation > 0)
                                index = Maco.currentJob.jobIdx;
                                Maco.debouncedSaveAll(0);
                            } else if (Maco.settings.addMotivation) {
                                lowMotivation = true;
                            }
                        }

                        if (
                            energyCondition(energyLimit) &&
                            (!Maco.isMotivationRequired() || (!lowMotivation && Maco.jobsBelowMotivation(result) <= result.length - 2 && Maco.totalMotivationLeft(result) >= energyLimit))
                        ) {
                            canAddEnergy = true;
                        }

                        Maco.loadJobsData(function() {
                            Maco.walkToJob(index, result);
                            if ((canAddEnergy || lowMotivation) || Maco.isRunning) {
                                setTimeout(function() {
                                    Maco.tryUseConsumable(result, 0, lowMotivation, canAddEnergy);
                                }, 1000);
                            }
                        });
                    });
                }
            });
        }, 0);
    };
    Maco.isDestinationReached = function(dest) {
        if (dest == null) return false;
        const from = Character.position;
        return Character.calcWayTo(dest) <= 0 || (from.x === dest.x && from.y === dest.y);
    };
    Maco.waitUntilDestinationIsReached = async function(destination) {
        if (destination == null) return false;
        while (!Maco.isDestinationReached(destination) && TaskQueue.queue.length > 0 && Maco.isRunning) {
            Maco.cancelSleep(true);
            await wait(interval_long);
        }
        return Maco.isDestinationReached(destination);
    };
    Maco.getPlayerProfileData = async function(playerId, playerName) {
        return await Ajax.remoteCallMode("profile", "init", {
            name: playerName,
            playerId: playerId
        }, function(resp) {
            if (resp.error) {
                new UserMessage(resp.message,UserMessage.TYPE_ERROR).show();
            }
            return resp;
        });
    };
    Maco.checkDuelProtection = async function(duration = 0) {
        const town = Character.homeTown;
        const isWanted = (await Maco.getPlayerProfileData(Character.playerId)).wanted;
        let isProtected = town.town_id == 0 && !isWanted;

        if ((town.town_id != 0 || isWanted) && Character.getDuelProtection(true) > new ServerDate().getTime()) {
            const protectionTime = (((Character.getDuelProtection(true) - new ServerDate().getTime()) / 1000) / 60); // minutes
            isProtected = protectionTime > duration;
            if (Maco.isDuelProtected && !isProtected) {
                Maco.showNotification("The West - Duel protection", `Duel protection ends in ${Math.floor(protectionTime)} minutes.`, "duel");
            }
        }

        Maco.isDuelProtected = isProtected;
        return isProtected;
    };
    Maco.moneyDepositAllowed = async function() {
        await Maco.checkDuelProtection(MIN_DUEL_PROTECTION);
        return Maco.settings.autoMoneyDeposit.enabled && (!Maco.settings.autoMoneyDeposit.duelProtected || !Maco.isDuelProtected);
    }
    Maco.walkToJob = async function(index, result, retry = 1) {
        if (walkToJob_running) {
            console.warn("%cDouble-call warning! Async function 'Maco.walkToJob' is already in progress.. return..", 'color: cyan');
            return;
        }
        walkToJob_running = true;

        try {
            const job = Maco.addedJobs.at(index);
            const jobGroup = JobList.getJobsByGroupId(job.groupId);
            const jobToWalkTo = jobGroup.map(j => {
                    const { id, workpoints, jobpoints } = JobsModel.getById(j.id);
                    const level = j.level;
                    return { id, workpoints, jobpoints, level }; // workpoints = required LP, jobpoints = character has LP
                })
                .reduce((prev, curr) => {
                    if (curr.jobpoints >= curr.workpoints && (curr.jobpoints - curr.workpoints) > (prev.jobpoints - prev.workpoints)) {
                        return curr;
                    }
                    return prev;
                });

            if (!Maco.isRunning) return;
            let taskError = false;
            let wayTime = Character.calcWayTo(job);
            Maco.destinyGuardian("walkToJob()", 4, 20000);

            if (await Maco.moneyDepositAllowed() && Character.money > Maco.settings.autoMoneyDeposit.amount) {
                const bidSuccess = await Maco.auctionDeposit(
                    Maco.settings.autoMoneyDeposit.auctionItemId,
                    Maco.settings.autoMoneyDeposit.sellerName
                );
                if (!bidSuccess && Maco.homeTown) {
                    wayTime = Character.calcWayTo(Maco.homeTown) + GameMap.calcWayTime(Maco.homeTown, job);
                    await Maco.goDepositMoney();
                }
            }

            function handleTaskError(msg) {
                taskError = true;

                if (retry > 0) {
                    Maco.showAlert(msg);
                } else {
                    Maco.showNotification("The West - Script has stopped", "Cannot travel to job.", "error");
                    Maco.handleButtonStopClick();
                }

                return EventHandler.ONE_TIME_EVENT;
            }

            EventHandler.listen('task_error', handleTaskError);
            TaskQueue.add(new TaskJob(jobToWalkTo.id, job.x, job.y, 15));
            await waitForEvent('taskqueue-ready');
            EventHandler.unlisten('task_error', handleTaskError);

            if (taskError) {
                if (retry > 0) {
                    await wait(timeout_regular);
                    await Maco.equipBestGear(jobToWalkTo.id, false, 0);
                    walkToJob_running = false;
                    await Maco.walkToJob(index, result, retry - 1);
                }
                return;
            }

            const advancedWalk = Maco.settings.advancedWalkingToJob && wayTime > 9 && Character.energy >= 8 && Character.level >= jobToWalkTo.level && Premium.hasBonus('automation');
            if (advancedWalk) {
                await wait(timeout_regular);
                Maco.prepareJobRun(index, result, true);
            }

            const xp = Character.experience;
            const arrived = await Maco.waitUntilDestinationIsReached(job);
            removeUiElement("ui-loader");

            if (Maco.isRunning) {
                if (arrived) {
                    Maco.stats.session.travelTime += Math.round(wayTime);
                } else if (xp !== Character.experience && Maco.settings.autoReload) {
                    Maco.reload("Destination not reached (walkToJob). Server error..?");
                }

                if (advancedWalk) return;
            }

            await Maco.cancelJobs();

            if (Maco.isRunning) {
                Maco.prepareJobRun(Maco.currentJob.jobIdx, result);
            }
        } catch (e) {
            const msg = "Exception occured in 'Maco.walkToJob': ";
            console.error(msg, e.stack);
            Maco.handleError(e, msg);
        } finally {
            walkToJob_running = false;
            Maco.updateRuntime();
        }
    };
    Maco.changeJob = function() {
        if (Maco.currentJob.direction) {
            Maco.currentJob.jobIdx++;
            if (Maco.currentJob.jobIdx === Maco.addedJobs.length) {
                Maco.currentJob.direction = false;
                Maco.currentJob.jobIdx--;
            }
        } else {
            Maco.currentJob.jobIdx--;
            if (Maco.currentJob.jobIdx < 0) {
                Maco.currentJob.direction = true;
                Maco.currentJob.jobIdx++;
            }
        }
    };
    Maco.runJob = async function(jobIndex, jobCount, walkingToJob = false, addEnergy = false, retry = 1) {
        if (runJob_running) {
            console.warn("%cDouble-call warning! Async function 'Maco.runJob' is already in progress.. return..", 'color: cyan');
            return;
        }
        runJob_running = true;

        try {
            var endJob = async function(oldXp, oldMoney) {
                Maco.stats.session.jobs -= TaskQueue.queue.length;
                Maco.stats.total.jobs -= TaskQueue.queue.length;
                await Maco.cancelJobs();
                Maco.updateStatistics(oldXp, oldMoney);
            }

            let taskError = false;
            function handleTaskError(msg) {
                taskError = !JobList.getJobById(Maco.addedJobs.at(jobIndex).id).canDo();
                return EventHandler.ONE_TIME_EVENT;
            }

            const job = Maco.addedJobs[jobIndex];
            const oldXp = Character.experience;
            const oldMoney = Character.money;
            Maco.destinyGuardian("Maco.runJob", 3, 30000);

            if (Maco.settings.addBuffs) {
                Maco.tryUseBuff();
            }

            const bestGearEquipped = await Maco.equipBestGear(job.id, walkingToJob);

            if (Maco.isRunning) {
                EventHandler.listen('task_error', handleTaskError);
                if (TaskQueue.busy && TaskQueue.toAdd.length > 0) {
                    TaskQueue.toAdd = [];
                    TaskQueue.busy = false;
                }
                const tasks = [];
                for (let i = 0; i < jobCount; i++) {
                    tasks.push(new TaskJob(job.id, job.x, job.y, 15));
                }
                TaskQueue.add(tasks);
                await waitForEvent('taskqueue-ready');
                EventHandler.unlisten('task_error', handleTaskError);

                Maco.stats.session.jobs += jobCount;
                Maco.stats.total.jobs += jobCount;

                await wait(timeout_long);
                const setEquip = await Maco.equipSet(job.set);

                if (taskError || (!setEquip.equipped && setEquip.error && Character.level > 19 && Maco.isRunning)) {
                    if (!bestGearEquipped && walkingToJob) {
                        Maco.settings.advancedWalkingToJob = false;
                        Maco.showAlert("Cannot equip set. ...Turning off 'Efficient Travel' setting!");
                    }
                    while (walkingToJob && walkToJob_running && Maco.isRunning) {
                        await wait(interval_long);
                    }
                    await endJob(oldXp, oldMoney);

                    if (retry > 0) {
                        (taskError) ? console.log("Problem starting job due low LP.. 'Maco.runJob' retry..")
                                    : console.log("Problem switching equip due low LP.. 'Maco.runJob' retry..");
                        runJob_running = false;
                        return await Maco.runJob(jobIndex, jobCount, false, addEnergy, retry - 1);
                    }

                    if (Array.from(Maco.sets.keys()).indexOf(job.set) > 2 && !Premium.hasBonus('automation')) {
                        for (let i = Maco.addedJobs.length - 1; i >= 0; i--) {
                            if (Maco.addedJobs[i].set === job.set) {
                                Maco.removeJob(Maco.addedJobs[i].x, Maco.addedJobs[i].y, Maco.addedJobs[i].id);
                            }
                        }
                    } else {
                        Maco.showAlert(Maco.alertTranslations[Maco.translationLang].alert_10(Maco.getJobName(job.id)));
                        Maco.removeJob(job.x, job.y, job.id);
                        (Maco.addedJobs.length > 2 && Maco.addedJobs.length <= MAX_ALLOWED_JOBS) ? Maco.makeRoute() : Maco.createRoute();
                    }
                    Maco.selectTab("addedJobs");

                    if (Maco.addedJobs.length === 0) {
                        Maco.sleep({ dontWakeUp: true, message: "No jobs to run." });
                    } else {
                        Maco.prepareJobRun(Maco.currentJob.jobIdx);
                    }

                    return;
                }

                if (walkingToJob && TaskQueue.queue.length > 1) {
                    let idx;
                    do {
                        if (TaskQueue.busy && Object.keys(TaskQueue.toCancel).length > 0) {
                            TaskQueue.toCancel = {};
                            TaskQueue.busy = false;
                        }
                        idx = TaskQueue.queue.at(0).type === 'job' ? 0 : 1;
                        TaskQueue.cancel(idx);
                        await waitForEvent('taskqueue-ready');
                    } while (TaskQueue.queue.length > 1 && TaskQueue.queue.at(idx).type === 'job' && TaskQueue.queue.at(idx).data.job.id !== job.id);
                }
            } else {
                return;
            }

            if (addEnergy) {
                const healthMissing = ((Character.maxHealth - Character.health) / Character.maxHealth) * 100;
                Maco.tryUseConsumable(Maco.lastResult, healthMissing, false, true);
            }

            let queueLength = TaskQueue.queue.length;
            const oldLevel = Character.level;

            while (Maco.isRunning) {
                if (TaskQueue.queue.length < queueLength) {
                    queueLength = TaskQueue.queue.length;
                    if (Character.level > oldLevel && Maco.farmingAssistant.enabled && Maco.farmingAssistant.stopLevel) {
                        Maco.showAlert("Level up.");
                        Maco.showNotification("The West - Script has stopped", "Level up.", "stopped");
                        Maco.handleButtonStopClick();
                        return;
                    }
                    const isSessionExpired = (
                        (
                            (Maco.build.nightBuild && Maco.canBuild()) || 
                            (Maco.settings.nightShiftWorker && Maco.favoriteJobs.length > 0)
                        ) && Maco.isSessionExpired()
                    ) || (
                        Character.level <= 19 &&
                        (Character.experience - oldXp > 0) &&
                        Maco.addedJobs.length === 2 &&
                        Maco.addedJobs.every(job => job.stopMotivation <= 0) &&
                        Maco.lastResultFarming[Maco.currentJob.jobIdx] === 0
                    );
                    if (isSessionExpired) {
                        break;
                    }
                }
                if (TaskQueue.queue.length === 0) {
                    Maco.updateStatistics(oldXp, oldMoney);
                    Maco.prepareJobRun(Maco.currentJob.jobIdx);
                    return;
                }
                if (Maco.isHealthBelowLimit()) {
                    break;
                }

                await wait(interval_long);
            }

            await endJob(oldXp, oldMoney);

            if (Maco.isRunning) {
                Maco.run();
            }
        } catch (e) {
            const msg = "Exception occured in 'Maco.runJob': ";
            console.error(msg, e.stack);
            Maco.handleError(e, msg);
        } finally {
            runJob_running = false;
        }
    };

    Maco.destinyGuardian = (function() {
        // Private object to store start times and execution counts for each target
        const guardianData = {};

        return function(target, maxRepetitions, timeWindow, stop = false) {
            if (!Maco.isRunning || !navigator.onLine) {
                return;
            }
            const currentTime = Date.now();

            if (!guardianData[target]) { // Initialize data for the target if it doesn't exist
                guardianData[target] = {
                    startTime: currentTime,
                    executions: 0
                };
            }

            const targetData = guardianData[target];

            if (currentTime - targetData.startTime >= timeWindow) { // Check if the time window has expired
                targetData.executions = 0;
                targetData.startTime = currentTime;
            }

            if (targetData.executions >= maxRepetitions) { // Check if the max repetitions limit has been reached
                const msg = `Destiny prevention! - Call limit '${target}'.`;
                if (stop || !Maco.settings.autoReload || Maco.diagnostics.reloadReasons[0]?.includes(msg)) {
                    Maco.showNotification("The West - Script has stopped", msg, "error");
                    Maco.handleButtonStopClick();
                } else {
                    Maco.reload(msg);
                }
                return;
            }

            targetData.executions++;
        };
    })();
    Maco.auctionDeposit = async function(itemId, sellerName) {
        if (!itemId || !sellerName) return false;
        const item = ItemManager.get(itemId);
        if (!item) return false;
        const ajaxKey = 'building_market';
        const searchKey = item.name;
        let searchResult = [];
        let page = 1;
        let next = true; // Start with the assumption there is a next page

        while (next) {
            const reqObj = {
                pattern: searchKey,
                nav: 'page',
                page: page,
                sort: 'bid', // bid, buynow
                order: 'asc',
                type: '',
                level_range_min: 1,
                level_range_max: 250,
                usable: true,
                has_effect: false,
                visibility: 2 // 2 - world, 1 - alliance, 0 - town
            };

            try {
                const response = await new Promise((resolve) => {
                    Ajax.remoteCall(ajaxKey, 'search', reqObj, (json) => {
                        (json.error) ? resolve(null) : resolve(json);
                    });
                });

                if (!response) break;

                if (response?.msg?.search_result) {
                    searchResult.push(...response.msg.search_result); // Merge results
                }
                next = Boolean(response?.msg?.next); // Check if there is another page
                page++; // Move to the next page

                if (next) await wait(generateRandomNumber(150, 250)); // Wait before next search request
            } catch (e) {
                break; // Exit loop for this key if an error occurs
            }
        }

        const filteredOffers = searchResult.filter(offer =>
            offer.auction_price != null && (offer.current_bid || offer.auction_price) + Character.money < Character.getCapital() &&
            offer.seller_name === sellerName
        );
        if (filteredOffers.length === 0) return false;
        const selectedOffer = filteredOffers.find(o => o.is_highest_bidder) || filteredOffers[0];

        try {
            await new Promise((resolve, reject) => {
                Ajax.remoteCall(ajaxKey, 'bid', {
                    bidtype: 0, // 0 - Use money on hand, 1 - Use money in bank
                    bid: (selectedOffer.current_bid || selectedOffer.auction_price) + Character.money,
                    market_offer_id: selectedOffer.market_offer_id
                }, function (resp) {
                    (resp.error) ? reject(resp) : resolve(resp);
                });
            });

            return true;
        } catch (error) {
            return false;
        }
    };
    Maco.goDepositMoney = async function(town = Maco.homeTown, amount = Character.money) { 
        if (town == null) return false;

        if (!Maco.isDestinationReached(town)) {
            TaskQueue.add(new TaskWalk(town.town_id, 'town'));
            await waitForEvent('taskqueue-ready');
        }

        (async () => {
            if (await Maco.waitUntilDestinationIsReached(town)) {
                Maco.depositMoney(town.town_id, amount);
            } else {
                console.warn("%cDestination to deposit money not reached within timeout.", 'color: cyan');
            }
        })();

        return true;
    };
    Maco.acceptMoneyDialog = function() {
        let dialogBox = document.querySelector('.tw2gui_dialog');
        if (dialogBox && dialogBox.querySelector('.twdb_banking')) {
            let yesButton = dialogBox.querySelector('.tw2gui_button:nth-child(1)');
            yesButton.click();
            return true;
        }
        return false;
    };
    Maco.depositMoney = function(townId = 1, amount = Character.money) {
        if (!Maco.acceptMoneyDialog()) {
            if (townId == null) townId = 1;
            if (amount < 20) return;
            try {
                globalWindow.BankWindow.townid = townId;
                globalWindow.BankWindow.DOM = new west.gui.Textfield("tb_balance_input_" + globalWindow.BankWindow.townid).setSize(10).setValue(amount).getMainDiv();
                globalWindow.BankWindow.Balance.add();
            } catch (e) {
                Ajax.remoteCall("building_bank", "deposit", {
                    town_id: townId,
                    amount: amount
                });
            }
        }
    };
    Maco.saveWayTimes = function(town = Maco.homeTown) {
        if (Maco.settings.fortBattle.selected < 0 || Maco.wayTimes || !Maco.battles.size || Maco.currentState !== 1 || town == null || !Maco.addedJobs.length) return;
        const jobs_town = [];
        const forts_town = new Map();
        let town_fort = 0;

        for (let i = 0; i < Maco.addedJobs.length; i++) {
            jobs_town[i] = GameMap.calcWayTime(Maco.addedJobs[i], town);
        }

        for (let i = 0; i < Maco.allianceForts.length; i++) {
            const fort = Maco.allianceForts[i];
            const time = GameMap.calcWayTime(fort, town);
            forts_town.set(fort.fort_id, time);
        }

        town_fort = GameMap.calcWayTime(town, Maco.battles.get(Maco.settings.fortBattle.selected));

        Maco.wayTimes = {
            town_fort,
            jobs_town,
            forts_town,
        };
    };
    Maco.canAttendBattle = function(traveling = false, town = Maco.homeTown) {
        if (Maco.isInBattle()) return true;
        const battleTimer = Maco.getCurrentBattleTimer(); // seconds

        if (Maco.settings.fortBattle.attend && Maco.battles.has(Maco.settings.fortBattle.selected) && battleTimer > 0) {
            const coolup = (Maco.totalMotivationLeft(Maco.lastResult) > 9 && Character.energy > 9 && !Maco.hasLowHealth())
                ? Math.max(0, 600 - Maco.getConsumeCooldown())
                : 0;
            const refill_time_reserve = (Maco.settings.fortBattle.refillHealth && Maco.currentState !== 3)
                ? (Maco.settings.fortBattle.isTank ? 1260 - coolup : 600 - coolup)
                : 0;
            const timeToGo = 120
                + Math.max(refill_time_reserve - battle_time_reserve, calcMaxPrepareTime())
                + battle_time_reserve
                + BATTLE_START_MARGIN;

            updateAllowedEnergy(battleTimer - timeToGo);

            if (battleTimer < timeToGo) {
                return true;
            }
        }

        function calcMaxPrepareTime() {
            const job = Maco.addedJobs[Maco.currentJob.jobIdx];
            const max_jobs_duration = 135; // 9 jobs * 15s = 135s
            let player_job_town = 0, player_town = 0, town_fort = 0, maxPrepareTime = 600;

            if (traveling && town != null) {
                player_job_town = GameMap.calcWayTime(Character.position, job) + GameMap.calcWayTime(job, town);
                town_fort = GameMap.calcWayTime(town, Maco.battles.get(Maco.settings.fortBattle.selected));
                player_town = GameMap.calcWayTime(Character.position, town);
                maxPrepareTime = Math.max(max_jobs_duration + player_town, player_job_town) + town_fort;
            } else if (Maco.wayTimes && town != null) {
                if (Maco.currentState !== 3) { // not sleeping
                    player_town = Maco.wayTimes.jobs_town[Maco.currentJob.jobIdx] + max_jobs_duration;
                } else if (TaskQueue.queue[0]?.type === 'fortsleep') { // is sleeping in fort
                    player_town = Maco.wayTimes.forts_town.get(TaskQueue.queue[0].data.fortId);
                }
                town_fort = Maco.wayTimes.town_fort;
                maxPrepareTime = player_town + town_fort;
            } else {
                maxPrepareTime = Math.min(maxPrepareTime, Character.calcWayTo(Maco.battles.get(Maco.settings.fortBattle.selected))) + max_jobs_duration;
            }

            return maxPrepareTime;
        }

        function updateAllowedEnergy(remnant) {
            if (remnant <= ((Character.energy - (Character.maxEnergy * (ENERGY_WASTE_TOLERANCE / 100))) * 15)) {
                Maco.maxAllowedEnergy = 0;
            } else if (remnant < Character.maxEnergy * 15) {
                Maco.maxAllowedEnergy = ENERGY_WASTE_TOLERANCE + (((remnant / 15) - Character.energy) / Character.maxEnergy) * 100;
            } else {
                Maco.maxAllowedEnergy = 100;
            }
        }

        return false;
    };
    Maco.isItemsBuffActive = function(item) {
        if (!CharacterSkills.buffs['items']) return false;
        return CharacterSkills.buffs['items'].fortbattle.offense == item.offense &&
            CharacterSkills.buffs['items'].fortbattle.defense == item.defense &&
            Number(CharacterSkills.buffs['items'].min_damage + "" + CharacterSkills.buffs['items'].max_damage) == item.battleDamage;
    };
    Maco.attendFortBattle = async function() {
        const battleSettings = Maco.settings.fortBattle;
        const calculateHealthPercent = (set) => Math.ceil((Character.health / (Maco.maxHealthForSet.get(set) || Character.maxHealth)) * 100); // returns HP %
        let refillHealthTokens = battleSettings.refillHealth ? (battleSettings.isTank ? 2 : 1) : 0;
        const fort = { ...Maco.battles.get(battleSettings.selected) };
        const battleSet = (fort.defense) ? battleSettings.defSet : battleSettings.attackSet;
        const getTimeLeft = () => (Maco.getCurrentBattleTimer(fort) - BATTLE_START_MARGIN);
        const battleStarted = () => Maco.getCurrentBattleTimer(fort) <= 0;
        let battleDurationTimeoutId = null;

        Maco.currentState = 5;
        Maco.selectTab("addedJobs");

        if (Maco.isInBattle()) {
            if (battleSettings.openFortWindow) {
                west.notification.fortBattle.openFort(fort.fortId);
            } else {
                closeBattleWindows();
            }

            EventHandler.listen('fort_battle_end', handleFortBattleEnd);
            EventHandler.listen("chat_room_removed", handleBattleRoomRemove);
            battleDurationTimeoutId = setTimeout(function() {
                EventHandler.signal('fort_battle_end', fort.fortId);
            }, BATTLE_MAX_DURATION * 60 * 1000); // minutes
            return;
        }

        Maco.showNotification("The West - Fort battle prepare", timestamp(), "battle_prep");

        const bidSuccess = await Maco.auctionDeposit(
            Maco.settings.autoMoneyDeposit.auctionItemId,
            Maco.settings.autoMoneyDeposit.sellerName
        );
        if (!Maco.isDestinationReached(fort)) {
            await Maco.equipSet(Maco.travelSet);
            if (!bidSuccess && Character.money > 1000) {
                await Maco.goDepositMoney();
            }
            Guidepost.start_walk(fort.fortId, 'fort');
            await waitForEvent('taskqueue-ready');
        }

        if (!Maco.maxHealthForSet.get(Maco.healthSet)) {
            await Maco.equipSet(Maco.healthSet);
        }
        await handleBattleSet(battleSet);

        while (refillHealthTokens > 0 && calculateHealthPercent(battleSet) < battleSettings.minHealth && getTimeLeft() > Maco.getConsumeCooldown()) {
            await wait(Maco.getConsumeCooldown() * 1000);
            if (calculateHealthPercent(battleSet) < battleSettings.minHealth) {
                await handleHealthRefill();
            } else {
                break;
            }
        }

        // Use battle consumable character/weapon buff or both
        const itemsBuff = Maco.allConsumables.find(item => item.hasBattleBonus && item.selected);
        const characterBuff = Maco.allConsumables.find(item => item.selected && ((fort.defense) ? item.settingTraps >= 50 : item.hiding >= 50));
        if (itemsBuff && !Maco.isItemsBuffActive(itemsBuff)) Maco.itemUse(itemsBuff.id, itemsBuff.name.trim() + " (Battle)");
        if (characterBuff && Maco.canAddBuff('character')) Maco.itemUse(characterBuff.id, characterBuff.name.trim() + " (Battle)");

        Maco.maxAllowedEnergy = 100;
        const arrived = await Maco.waitUntilDestinationIsReached(fort);
        if (!arrived && TaskQueue.queue.length === 0 && Maco.isRunning && !battleStarted()) {
            Maco.attendFortBattle();
            return;
        }

        executeAfterBattleTimer(() => {
            if (arrived) {
                if (battleSettings.openFortWindow) {
                    west.notification.fortBattle.openFort(fort.fortId);
                } else {
                    closeBattleWindows();
                }

                Maco.showNotification("The West - Fort battle started", timestamp(), "battle");
                EventHandler.listen('fort_battle_end', handleFortBattleEnd);
                EventHandler.listen("chat_room_removed", handleBattleRoomRemove);
                battleDurationTimeoutId = setTimeout(function() {
                    EventHandler.signal('fort_battle_end', fort.fortId);
                }, BATTLE_MAX_DURATION * 60 * 1000); // minutes
            } else {
                Maco.showAlert("Missed fort battle. Continuing jobs.. :(");
                Maco.cancelJobsPromise().then(() => {
                    Maco.startTime = new Date();
                    Maco.run();
                });
            }
        });

        function executeAfterBattleTimer(callback) {
            const timer = Maco.getCurrentBattleTimer(fort);
            if (timer <= 0 && Maco.isRunning) {
                callback();
                return;
            }
            const timeoutId = setTimeout(() => {
                if (!Maco.isRunning) {
                    clearTimeout(timeoutId);
                    return;
                }
                callback();
            }, (timer * 1000) + 10000);
        }

        function sortByBetterHealth(consumes, refillAmount) {
            // First, try to find consumables strictly above refillAmount
            const above = consumes.filter(c => c.health >= refillAmount);
            if (above.length > 0) {
                return above.sort((a, b) => {
                    if (a.health !== b.health) return a.health - b.health; // closest above refillAmount
                });
            }

            // Otherwise, fall back to "closest to refillAmount" logic
            return sortByHealthMissing(consumes, refillAmount);
        }

        async function handleHealthRefill() {
            const missingBattleHealth = 100 - calculateHealthPercent(battleSet); // amount in %
            const fortMedicine = Maco.allConsumables.find(item => item.id == 54382000);
            const HPbuff = battleSettings.isTank && Character.maxHealth > 5000 && refillHealthTokens > 1 && (Maco.canAddBuff('character') || battleSettings.overwriteCharacterBonus) && fortMedicine?.selected; // fort medicine
            const fortMedicineRefill = HPbuff && fortMedicine?.health + calculateHealthPercent(battleSet) >= battleSettings.minHealth;
            const equipHealthSet = !fortMedicineRefill && (missingBattleHealth > 10 && calculateHealthPercent(Maco.healthSet) < calculateHealthPercent(battleSet));
            const refillAmount = (equipHealthSet)
                ? (await Maco.calcHealthRefill(battleSet) || missingBattleHealth)
                : missingBattleHealth;
            //const itemToUse = (HPbuff) ? fortMedicine : (refillAmount >= 1) ? Maco.tryFindConsumable(0, 0, refillAmount, false, false, true) : null;
            const selectedConsumes = Maco.allConsumables.filter(c =>
                c.selected && c.count > 0 && c.health > 0 && (!c.hasCharacterBonus || battleSettings.overwriteCharacterBonus)
            );
            const itemToUse = (HPbuff) ? fortMedicine
                : (refillAmount >= 1)
                    ? (refillHealthTokens >= 2)
                        ? equalValuesOnly(sortByHealthMissing(selectedConsumes, refillAmount), 'health').sort((a, b) => a.energy - b.energy)[0]
                        : equalValuesOnly(sortByBetterHealth(selectedConsumes, refillAmount), 'health').sort((a, b) => a.energy - b.energy)[0]
                    : null;

            if (itemToUse && refillAmount >= 1) {
                Maco.useConsumable(itemToUse, false, false, true, equipHealthSet);
                await wait(timeout_regular);
                while (Maco.currentState === 2 && Maco.isRunning) {
                    await wait(interval_long);
                }
                Maco.currentState = 5;
                refillHealthTokens -= 1;
            } else {
                refillHealthTokens = 0;
            }

            await handleBattleSet(battleSet);
        }

        function handleFortBattleEnd(fortId) {
            if (fortId != fort.fortId) {
                return false;
            }
            clearTimeout(battleDurationTimeoutId);
            EventHandler.unlisten("chat_room_removed", handleBattleRoomRemove);

            setTimeout(function () {
                if (Maco.dailyQuests.enabled) {
                    Maco.runDailyQuests();
                }
                if (Maco.currentState === 5 && Maco.isRunning) {
                    Maco.cancelJobsPromise().then(() => {
                        setTimeout(function() {
                            closeBattleWindows();
                        }, 60000);
                        Maco.updateFortBattles();
                        Maco.startTime = new Date();
                        Maco.currentState = 1;
                        Maco.run();
                    });
                }
            }, 5000);

            return EventHandler.ONE_TIME_EVENT;
        }

        function handleBattleRoomRemove(room) {
            if (room.battleData?.isFinished && room.fortId == fort.fortId) {
                EventHandler.signal('fort_battle_end', room.fortId);

                return EventHandler.ONE_TIME_EVENT;
            }
        }

        function closeBattleWindows() {
            const cemeteryCloseButton = document.querySelector('.cemetery .tw2gui_window_buttons_close');
            const battleSelector = `.fortbattle-${fort.fortId} .tw2gui_window_buttons_close`;
            const battleCloseButton = document.querySelector(battleSelector);
            if (battleCloseButton) battleCloseButton.click();
            if (cemeteryCloseButton) cemeteryCloseButton.click();
        }

        async function handleBattleSet(battleSet, retries = 1) {
            if (Maco.sets.has(battleSet)) {
                return (await Maco.equipSet(battleSet)).equipped;
            }

            const wardrobeSet = Maco.wardrobe.get(battleSet);
            if (wardrobeSet != undefined) {
                for (let attempt = 0; attempt <= retries; attempt++) {
                    const result = await Maco.equipSet(wardrobeSet.id);
                    if (result.equipped) return true;
                }
                return false;
            }

            const isTank = battleSettings.isTank;
            const gear = fort.defense
                ? isTank
                    ? { leadership: 100, pitfall: 150, health: 150, dodge: 100 }
                    : { leadership: 125, pitfall: 150, aim: 100 }
                : isTank
                    ? { leadership: 100, hide: 150, health: 150, dodge: 100 }
                    : { leadership: 125, hide: 150, aim: 100 };

            const finished = await Maco.equipBestCustomGear(gear);
            if (finished) Maco.maxHealthForSet.set(battleSet, Character.maxHealth);
            return finished;
        }
    };
    Maco.isInBattle = function() {
        Maco.updateFortBattles();
        const battle = Maco.battles.get(Maco.settings.fortBattle.selected);
        if (!battle) return false;
        const battleSeconds = Math.floor((battle.start + Game.clientTimedrift - new Date().getTime()) / 1000);
        return battleSeconds <= 0 && Maco.isDestinationReached(battle);
    };
    Maco.getCurrentBattleTimer = function(fort = Maco.battles.get(Maco.settings.fortBattle.selected)) { // in seconds
        if (!fort) return 0;
        const battleSeconds = Math.floor((fort.start + Game.clientTimedrift - new Date().getTime()) / 1000);
        return Math.max(battleSeconds, 0);
    };
    Maco.updateFortBattles = function(newBattle) {
        const battleRooms = Maco.getBattleRooms();
        const noActiveBattles = battleRooms.every(room => room.battleData.isFinished) || !west.notification.fortBattle._timer;

        if (!Maco.settings.fortBattle.attend || noActiveBattles) {
            Maco.battles = new Map();
            Maco.settings.fortBattle.selected = -1;
            Maco.maxAllowedEnergy = 100;
            return;
        }

        const battles = battleRooms
            .filter(room => !room.battleData.isFinished)
            .reduce((map, { title, fortId, battleData: { x, y, start, defense } }) => {
                map.set(fortId, { title, fortId, x, y, start, defense });
                return map;
            }, new Map());

        Maco.battles = battles;
        const selected = Maco.settings.fortBattle.selected;
        const firstFortId = battles.keys().next().value; // Get first fortId
        const isInvalidSelection = selected === -1 || !battles.has(selected);
        const soonerNewBattle = newBattle?.fortId === firstFortId;

        if (battles.size > 0 && (isInvalidSelection || soonerNewBattle)) {
            Maco.settings.fortBattle.selected = firstFortId;
        }
    };
    Maco.getBattleRooms = function() { 
        const rooms = Chat.Resource.Manager.getRooms();
        const battleRooms = [];
        
        for (let roomId in rooms) {
            const room = rooms[roomId];
            if (room instanceof Chat.Resource.RoomFortBattle) {
                battleRooms.push(room);
            }
        }

        // Sort battleRooms by room.battleData.start in ascending order
        battleRooms.sort((a, b) => a.battleData.start - b.battleData.start);

        return battleRooms;
    };
    Maco.getBattleRoomByFortId = function(fortId) {
        const rooms = Chat.Resource.Manager.getRooms();
        for (let roomId in rooms) {
            const room = rooms[roomId];
            if (room instanceof Chat.Resource.RoomFortBattle && room.fortId == fortId) {
                return room;
            }
        }
        return null;
    };
    Maco.getClosestFort = function(fortsArray) {
        return new Promise((resolve) => {
            const forts = [...Object.values(fortsArray)]; // Clone array so we can mutate it safely

            function tryNext() {
                if (forts.length === 0) {
                    return resolve(null); // No valid fort found
                }

                // Get closest fort
                const closest = forts.reduce((closest, fort) => {
                    const time = Character.calcWayTo(fort);
                    return !closest || time < Character.calcWayTo(closest) ? fort : closest;
                }, null);

                if (!closest) return resolve(null);

                // Check barrack stage
                Ajax.remoteCallMode("fort_building_barracks", "index", { fort_id: closest.fort_id }, function(data) {
                    if (!data.error && data.barrackStage >= 4) {
                        resolve(closest); // Valid fort found
                    } else {
                        // Remove this fort and try next
                        const index = forts.findIndex(f => f.fort_id === closest.fort_id);
                        if (index !== -1) forts.splice(index, 1);
                        tryNext();
                    }
                });
            }

            tryNext();
        });
    };
    Maco.getClosestTown = async function() {
        return new Promise((resolve, reject) => {
            console.time("Execution Time");
            const towns = []; // Initialize an empty array to hold the towns

            Ajax.get('map', 'get_minimap', {}, function (json) {
                if (json.error) {
                    return reject(new UserMessage(json.msg).show()); // Reject the promise if there's an error
                }

                for (const i of Object.keys(json.towns)) {
                    const town = json.towns[i];

                    if (town.member_count > 0) {
                        town._waytime = GameMap.calcWayTime(Character.position, {x: town.x, y: town.y}); // Store the calculated waytime in the town object
                        towns.push(town); // Add the town to the array if it has members
                    }
                }

                towns.sort((a, b) => a._waytime - b._waytime); // Sort towns by calculated waytime

                const processTown = function (index) {
                    if (index >= towns.length) {
                        return resolve(null); // Resolve with null if no town with level 5 hotel is found
                    }

                    const town = towns[index];

                    // AJAX call to get the hotel level for the town
                    Ajax.remoteCallMode('building_hotel', 'get_data', { town_id: town.town_id }, function (data) {
                        if (data.error) {
                            return reject(new UserMessage(data.msg).show()); // Reject the promise if there's an error
                        }

                        const hotelLevel = data.hotel_level || 0;

                        if (hotelLevel === 5) {
                            return resolve(town); // Resolve the promise with the closest town with level 5 hotel
                        } else {
                            processTown(index + 1); // Recursively process the next town
                        }
                    });
                };

                if (towns.length > 0) {
                    processTown(0); // Start processing the first town
                } else {
                    resolve(null); // Resolve with null if no towns are available
                }
            });
        });
    };
    Maco.addWaitingReason = function(reason) {
        Maco.diagnostics.waitingReasons.push(reason);
        if (Maco.diagnostics.waitingReasons.length > 50) {
            Maco.diagnostics.waitingReasons.shift();
        }
    };
    Maco.getCharacterInfo = function(callback) {
        Ajax.remoteCallMode('character', 'get_info', {}, function(resp) {
            callback(resp);
        });
    };
    Maco.sleep = async function(options = {}) {
        const { dontWakeUp = false, message = "", flag = "" } = options;
        const calculateEnergyMissing = () => 100 - (Character.energy / Character.maxEnergy) * 100;
        const calculateHealthLimit = () => Math.min((Maco.maxHealthForSet.get(Maco.addedJobs[Maco.currentJob.jobIdx]?.set) || Character.maxHealth) * 0.4, Maco.settings.healthStopValue * 2);
        const isEnoughHealth = () => Character.health >= (Maco.maxHealthForSet.get(Maco.addedJobs[Maco.currentJob.jobIdx]?.set) || (Character.maxHealth * 0.5));
        const sleepCondition = () => (flag === "health") ? !isEnoughHealth() : (calculateEnergyMissing() !== 0 || !isEnoughHealth());

        async function monitorCharacterSleep() {
            const sleepTime = new Date();
            let attendingBattle = false;
            let intervalId = setInterval(() => {
                Maco.getCharacterInfo(function(data) {
                    Character.energy = data.energyCurrent;
                    Character.health = data.healthCurrent;
                });
            }, 5 * 60 * 1000); // 5 minutes in milliseconds

            try {
                while (Maco.currentState === 3 && sleepCondition()) {
                    if (Maco.canAttendBattle()) {
                        attendingBattle = true;
                        await Maco.cancelJobs();
                        Maco.attendFortBattle();
                        break;
                    }

                    await wait(timeout_long);
                }
            } finally {
                clearInterval(intervalId);

                if (!attendingBattle) {
                    const sleepDuration = calculateElapsedSeconds(sleepTime);
                    Maco.stats.session.sleepTime += sleepDuration;
                    Maco.addWaitingReason(`Sleep regenerating: ${sleepDuration / 60} minutes.`);
                    Maco.updateRuntime();

                    if (Maco.currentState === 3) {
                        await Maco.cancelJobs();
                        Maco.run();
                    }
                }
            }
        }

        if (Maco.settings.enableRegeneration && (dontWakeUp || (calculateEnergyMissing() !== 0 || Maco.isHealthBelowLimit(calculateHealthLimit())))) {
            Maco.currentState = 3;
            Maco.selectTab("addedJobs");
            if (!dontWakeUp && message) Maco.showNotification("The West - Script has paused", message, 'sleep');

            const closestFort = await Maco.getClosestFort(Maco.allianceForts);
            let closestTown = null;
            if (!closestFort) {
                closestTown = await Maco.getClosestTown();
            }

            if (!Maco.isDestinationReached(closestFort || closestTown)) {
                await Maco.equipSet(Maco.travelSet);
                Maco.saveWayTimes();
            }

            TaskQueue.add(
                closestFort
                    ? new TaskFortSleep(closestFort.fort_id, closestFort.x, closestFort.y)
                    : new TaskSleep(closestTown.town_id, "luxurious_apartment")
            );

            await waitForEvent('taskqueue-ready');
            (Maco.regenerationSet !== -1) ? Maco.equipSet(Maco.regenerationSet) : Maco.equipSet(Maco.healthSet);

            await Maco.waitUntilDestinationIsReached(closestFort || closestTown);

            if (Maco.isDestinationReached(Maco.homeTown) && await Maco.moneyDepositAllowed()) {
                Maco.depositMoney(Maco.homeTown.town_id);
            }

            if (dontWakeUp) {
                Maco.finishRun(message);
                return;
            }

            await monitorCharacterSleep();
        } else if (Maco.maxAllowedEnergy < 100 && Maco.settings.fortBattle.attend && Maco.battles.has(Maco.settings.fortBattle.selected)) {
            Maco.attendFortBattle();
        } else {
            Maco.finishRun(message);
        }
    };
    Maco.loadBuildingData = async function(town, building) {
        if (town.town_id == 0) return null;
        return new Promise((resolve, reject) => {
            Ajax.remoteCallMode("cityhall_build", "build", {
                x: town.x,
                y: town.y,
                building: building
            }, function(json) {
                if (json.error) {
                    new UserMessage(json.msg, UserMessage.TYPE_ERROR).show();
                    reject(null);
                } else {
                    resolve(json); // Resolve the promise with the received data
                }
            });
        });
    };
    Maco.buildTownBuilding = async function(building, duration, hours) { // Allowed durations: 3600, 1800, 900
        Maco.currentState = 7;
        Maco.isRunning = true;
        Maco.refreshTab();
        const energyCostBefore = Maco.energyCost;
        const town = Character.homeTown;
        const buildingData = await Maco.loadBuildingData(town, building);
        if (!buildingData) {
            handleBuildEnd();
            return;
        }

        const minMotivation = 88;
        const skillsObject = Object.fromEntries(buildingData.build_skills.skills.map(s => [s.skill, s.coefficient]));
        const maxJobs = Premium.hasBonus('automation') ? TaskQueue.limit.premium : TaskQueue.limit.normal;
        const divisor = duration === 3600 ? 12 : duration === 1800 ? 6 : 3;
        Maco.energyCost = divisor;
        let motivation = buildingData.motivation * 100;
        let remainingJobs = (hours) ? ((3600 / duration) * hours) : Number.MAX_VALUE;
        let totalAddedTasks = 0;
        let taskError = false;

        if (!Maco.isDestinationReached(town)) {
            await Maco.equipSet(Maco.travelSet);
            await Maco.goDepositMoney(town);
        } else {
            Maco.depositMoney(town.town_id);
        }

        (Maco.build.set < 0)
            ? await Maco.equipBestCustomGear(skillsObject)
            : await Maco.equipSet(Maco.build.set);

        while ((Maco.currentState === 7 || Maco.isRunning) && (remainingJobs > 0 || TaskQueue.queue.length > 0 || totalAddedTasks > 0)) {
            const currentQueue = TaskQueue.queue.length;

            if (currentQueue <= 1 && Maco.settings.addEnergy && Character.energy < divisor && !taskError) { // Energy refill
                await handleEnergyRefill(motivation);
            }

            if (totalAddedTasks - currentQueue === 1 && !taskError) { // Handle case where one task successfully finished
                totalAddedTasks -= 1;
                motivation -= divisor;
                if (Maco.settings.addMotivation && motivation <= minMotivation) {
                    motivation = await handleMotivationRefill(motivation);
                }
            } else if (currentQueue === 0 && totalAddedTasks > 0) { // Handle unexpected clearing of all tasks (gets KO, not enough LP, task error)
                remainingJobs += totalAddedTasks;
                totalAddedTasks = 0;
            }

            const tasksToAdd = Math.min(
                Math.floor(Character.energy / divisor),
                maxJobs - currentQueue,
                remainingJobs
            );

            if (tasksToAdd > 0) { // Add new tasks
                EventHandler.listen('task_error', handleTaskError);
                build(tasksToAdd);
                await waitForEvent('taskqueue-updated');
                EventHandler.unlisten('task_error', handleTaskError);

                if (taskError && TaskQueue.queue.length === 0) {
                    if (Maco.build.set >= 0) {
                        Maco.build.set = -1;
                        await Maco.equipBestCustomGear(skillsObject)
                    } else {
                        break;
                    }
                }

                remainingJobs -= tasksToAdd;
                totalAddedTasks += tasksToAdd;
            }

            await wait(5000);
        }

        handleBuildEnd();

        async function handleEnergyRefill(currentMotivation) {
            let consumable = Maco.tryFindConsumable(-1, 0, 0, false, true, false);
            const consumUsed = Maco.settings.addEnergyOptional && consumable && Maco.canUseConsume(consumable.id) &&
                await Maco.useConsumable(consumable, false, true, false); // Optional energy

            if (!consumUsed && TaskQueue.queue.length === 0) {
                consumable = Maco.tryFindConsumable(-1, 100 - currentMotivation, 0, false, false, false);
                if (consumable) await Maco.useConsumable(consumable, false, true, false);
            }
        }

        async function handleMotivationRefill(currentMotivation) {
            const consumable = Maco.tryFindConsumable(-1, 100 - currentMotivation, 0, true, false, false);

            if (consumable && Maco.canUseConsume(consumable.id)) {
                Maco.useConsumable(consumable, true, false, false);
                return Math.min(100, currentMotivation + consumable.motivation);
            }

            return currentMotivation;
        }

        function handleTaskError(msg) {
            taskError = true;
            Maco.showAlert(buildingData.build_name + ": " + msg);
            return EventHandler.ONE_TIME_EVENT;
        }

        function build(amount) {
            if (TaskQueue.busy && TaskQueue.toAdd.length > 0) {
                TaskQueue.toAdd = [];
                TaskQueue.busy = false;
            }
            const tasks = [];
            for (let i = 0; i < amount; i++) {
                tasks.push(new TaskBuild(town.x, town.y, building, duration, "town"));
            }
            TaskQueue.add(tasks);
        }

        function handleBuildEnd() {
            Maco.energyCost = energyCostBefore || Maco.energyCost;
            if (Maco.currentState === 7) {
                Maco.isRunning = false;
                if (Maco.addedJobs.length === 0 && !Maco.swapSilverJobs()) {
                    Maco.sleep({ dontWakeUp: true, message: "No jobs to run." });
                } else {
                    Maco.handleScriptStart();
                }
            }
        }
    };
    Maco.setWorkerProfile = function(profile) {
        if (profile == undefined) {
            if (Maco.favoriteJobs.length > 0 && Maco.workerProfiles["profile0"].jobs.length === 0 && Maco.workerProfiles.selected === "profile0") {
                Maco.workerProfiles["profile0"].jobs = Maco.favoriteJobs;
                Maco.workerProfiles["profile0"].maxJobRank = Maco.settings.maxJobRank;
                Maco.workerProfiles["profile0"].jobsToAdd = Maco.settings.jobsToAdd;
                return;
            }
            Maco.favoriteJobs = Maco.workerProfiles[Maco.workerProfiles.selected].jobs;
        } else {
            Maco.workerProfiles.selected = profile;
            Maco.favoriteJobs = Maco.workerProfiles[profile].jobs;
        }
    };
    Maco.canBuild = function() {
        return Maco.build.allowed && Character.homeTown.town_id !== 0;
    };
    Maco.localStorageSet = function(key, value) {
        localStorage.setItem(`Maco_${characterId}_${key}`, value);
    };
    Maco.localStorageGet = function(key) {
        return localStorage.getItem(`Maco_${characterId}_${key}`);
    };
    Maco.localStorageRemove = function(key) {
        localStorage.removeItem(`Maco_${characterId}_${key}`);
    };
    Maco.deleteCookie = function(key) {
        document.cookie = key + '=; expires=Thu, 01 Jan 1970 00:00:00 UTC; path=/;';
    };
    Maco.isSessionExpired = function(toDate = getUTCDate()) {
        const currentHour = new Date().getUTCHours(); // This is important to get correct UTC hours in all timezones and browsers with any VPN.
        const currentMinute = toDate.getMinutes();
        const currentSecond = toDate.getSeconds();
        const expireHour = 1; // UTC
        const expireMinute = 0;
        return (currentHour >= expireHour && currentMinute >= expireMinute && currentSecond >= SESSION_EXPIRE_SECOND) &&
            Maco.lastReloadTime < new Date(toDate).setHours(expireHour, expireMinute, SESSION_EXPIRE_SECOND);
    };
    Maco.saveAll = function() {
        const currentDate = getUTCDate();
        const expireHour = 1; // UTC
        const expireMinute = 0;
        const cookieExpireTime = Maco.localStorageGet('cookieExpireTime');
        const cookieExpired = (cookieExpireTime) ? currentDate >= new Date(cookieExpireTime) : true;
        let expiracyDateTemporary;
        let needReload = false;

        if (cookieExpired || Character.level <= 19) {
            expiracyDateTemporary = getUTCDate();
            expiracyDateTemporary.setHours(expireHour, expireMinute, SESSION_EXPIRE_SECOND);
            expiracyDateTemporary.setDate(new Date().getUTCDate() + ((Character.level <= 19) ? 2 : 1)); // Expiry day is next day, or in 2 days when low level.
            Maco.localStorageSet('cookieExpireTime', expiracyDateTemporary);
        } else {
            expiracyDateTemporary = new Date(cookieExpireTime);
        }

        if (Maco.isRunning && !Maco.farmingAssistant.awaitNextSession && Maco.isSessionExpired(currentDate) &&
            ((Maco.settings.nightShiftWorker && Maco.favoriteJobs.length > 0) || (Maco.build.nightBuild && Maco.canBuild()))
        ) {
            Maco.addedJobs = [];
            needReload = true;
        }

        const jobFilterCopy = { ...Maco.jobFilter, filterJob: "" };
        const jobsToSave = [];
        if (!cookieExpired || (!Maco.settings.nightShiftWorker || Maco.favoriteJobs.length === 0) || Maco.farmingAssistant.awaitNextSession) {
            Maco.addedJobs.forEach(function(job) {
                let jobForm = {
                    x: job.x,
                    y: job.y,
                    id: job.id,
                    groupId: job.groupId,
                    silver: job.silver,
                    motivation: job.motivation,
                    stopMotivation: job.stopMotivation,
                    set: job.set
                };
                jobsToSave.push(jobForm);
            });
        }
        /*const temporaryObject = {
            currentJob: Maco.currentJob,
            addedJobs: jobsToSave
        };*/
        const sessionObject = {
            sessionStats: Maco.stats.session,
            diagnostics: Maco.diagnostics,
            currentJob: Maco.currentJob,
            addedJobs: jobsToSave
        };
        const permanentObject = {
            jobFilterPreferences: jobFilterCopy,
            sortJobTable: Maco.sortJobTable,
            farmingAssistant: Maco.farmingAssistant.enabled,
            build: Maco.build,
            settings: Maco.settings,
            consumablesSelection: Maco.consumablesSelection,
            favoriteJobs: Maco.favoriteJobs,
            workerProfiles: Maco.workerProfiles,
            dailyQuests: Maco.dailyQuests,
            jobsFarmingGear: Maco.jobsFarmingGear,
            totalStats: Maco.stats.total,
            travelSet: Maco.travelSet,
            jobSet: Maco.jobSet,
            healthSet: Maco.healthSet,
            regenerationSet: Maco.regenerationSet
        };

        //const jsonTemporary = encodeURIComponent(JSON.stringify(temporaryObject));
        const jsonSession = encodeURIComponent(JSON.stringify(sessionObject));
        const jsonSettings = encodeURIComponent(JSON.stringify(permanentObject, replacer));
        Maco.localStorageSet('sessionData', jsonSession);
        Maco.localStorageSet('data', jsonSettings);
        //document.cookie = `Maco_${characterId}=${jsonTemporary};expires=${expiracyDateTemporary};SameSite=None;Secure;`;
        if (needReload && Maco.isRunning) {
            if (Maco.relogAllowed()) {
                Maco.relog("Daily jobs reset (relogged). ");
            } else {
                Maco.reload("Daily jobs reset (reloaded). ");
            }
        }
    };
    (function waitForLinearQuestHandlerFactory() {
        const gameURL = /^https:\/\/.*\.the-west\..*\/game\.php/;
        if (!gameURL.test(document.URL)) return;

        const startTime = performance.now();
        const pollInterval = 50;
        const maxWait = 6000; // Maximum time to wait in ms

        function waitForLinearQuestHandler() {
            const elapsed = performance.now() - startTime;

            if (elapsed > maxWait) {
                console.log(`[Maco] Gave up waiting for LinearQuestHandler after ${Math.round(elapsed)} ms`);
                return;
            }

            if (typeof LinearQuestHandler?.init !== 'function') {
                return setTimeout(waitForLinearQuestHandler, pollInterval);
            }

            console.log(`[Maco] LinearQuestHandler.init became available after ${Math.round(elapsed)} ms`);

            let data = Maco.localStorageGet('data');
            let permanentObject = data ? JSON.parse(decodeURIComponent(data), reviver) : null;
            if (!permanentObject?.settings?.skipTutorial) return;

            proxyMethod(LinearQuestHandler, "init", ({ target, thisArg, args }) => {
                EventHandler.signal("tutorial_finished");
                return;
            });
        }

        waitForLinearQuestHandler();
    })();
    Maco.loadSavedData = function() {
        const cookieExpireTime = Maco.localStorageGet('cookieExpireTime');
        const cookieExpired = (cookieExpireTime) ? getUTCDate() >= new Date(cookieExpireTime) : true;
        const sessionObject = (!cookieExpired && Maco.localStorageGet('sessionData')) ? JSON.parse(decodeURIComponent(Maco.localStorageGet('sessionData'))) : null;
        let data = Maco.localStorageGet('data');
        const permanentObject = data ? JSON.parse(decodeURIComponent(data), reviver) : null;

        if (sessionObject) {
            Maco.addedJobs = [];
            const tmpAddedJobs = sessionObject.addedJobs || [];
            for(let j = 0; j < tmpAddedJobs.length; j++) {
                const jobP = new JobPrototype(tmpAddedJobs[j].x, tmpAddedJobs[j].y, tmpAddedJobs[j].id, tmpAddedJobs[j].groupId, tmpAddedJobs[j].silver);
                jobP.distance = 0;
                jobP.setMotivation(tmpAddedJobs[j].motivation);
                jobP.setStopMotivation(tmpAddedJobs[j].stopMotivation);
                jobP.setSet(tmpAddedJobs[j].set);
                Maco.addedJobs.push(jobP);
            }
            Maco.addedJobsOld = [...Maco.addedJobs];
            assignObjects(Maco.currentJob, sessionObject.currentJob);

            Maco.stats.session = sessionObject.sessionStats ?? Maco.stats.session;
            Maco.diagnostics = sessionObject.diagnostics ?? Maco.diagnostics;
            for (var key in sessionObject.diagnostics) {
                if (sessionObject.diagnostics.hasOwnProperty(key) && sessionObject.diagnostics[key] != undefined) {
                    Maco.diagnostics[key] = sessionObject.diagnostics[key];
                    if (Array.isArray(Maco.diagnostics[key]) && Maco.diagnostics[key].length > 5000) { // Empty arrays exceeding "too many" items
                        Maco.diagnostics[key] = [];
                    }
                }
            }
        }

        if (permanentObject) {
            // Objects
            assignObjects(Maco.settings, permanentObject.settings);
            assignObjects(Maco.build, permanentObject.build);
            assignObjects(Maco.jobFilter, permanentObject.jobFilterPreferences);
            assignObjects(Maco.sortJobTable, permanentObject.sortJobTable);
            assignObjects(Maco.stats.total, permanentObject.totalStats);
            assignObjects(Maco.workerProfiles, permanentObject.workerProfiles);
            assignObjects(Maco.dailyQuests, permanentObject.dailyQuests);
            // Arrays
            Maco.jobsFarmingGear = permanentObject.jobsFarmingGear ?? Maco.jobsFarmingGear;
            Maco.favoriteJobs = permanentObject.favoriteJobs ?? Maco.favoriteJobs;
            Maco.consumablesSelection = permanentObject.consumablesSelection ?? Maco.consumablesSelection;
            // Other variables
            Maco.farmingAssistant.enabled = permanentObject.farmingAssistant ?? Maco.farmingAssistant.enabled;
            Maco.travelSet = permanentObject.travelSet ?? Maco.travelSet;
            Maco.jobSet = permanentObject.jobSet ?? Maco.jobSet;
            Maco.healthSet = permanentObject.healthSet ?? Maco.healthSet;
            Maco.regenerationSet = permanentObject.regenerationSet ?? Maco.regenerationSet;
            // Methods
            Maco.setSetForAllJobs();
            Maco.setWorkerProfile();
        }
    };
    Maco.exportSettings = function() {
        Maco.saveAll();
        var data = Maco.localStorageGet('data');
        var wardrobe = localStorage.getItem('TWCalc_Wardrobe'); // Get wardrobe if exists

        var exportData = {
            macoData: JSON.parse(decodeURIComponent(data), reviver),
            wardrobe: (wardrobe && Maco.settings.allowWardrobeExport) ? JSON.parse(wardrobe) : null
        };
        var jsonExport = encodeURIComponent(JSON.stringify(exportData, replacer));

        var fileName = `Maco_data_${Character.name}.json`;
        var blob = new Blob([jsonExport], { type: 'application/json' });
        var link = document.createElement('a');
        link.href = URL.createObjectURL(blob);
        link.download = fileName;

        document.body.appendChild(link);
        link.click();
        document.body.removeChild(link);
        setTimeout(() => URL.revokeObjectURL(link.href), 0); // Small delay to ensure download starts
    };
    Maco.importSettings = function() {
        return new Promise((resolve, reject) => {
            var input = document.createElement('input');
            input.type = 'file';
            input.accept = '.json';

            input.onchange = function(event) {
                var file = event.target.files[0];
                if (!file) {
                    reject(new Error('No file selected.'));
                    return;
                }

                var reader = new FileReader();
                reader.onload = function(e) {
                    try {
                        var jsonData = JSON.parse(decodeURIComponent(e.target.result));

                        if (jsonData.macoData) {
                            Maco.localStorageSet('data', encodeURIComponent(JSON.stringify(jsonData.macoData, replacer)));
                        }/* else if (jsonData.dusanData) { // #compatibility
                            Maco.localStorageSet('data', encodeURIComponent(JSON.stringify(jsonData.dusanData, replacer)));
                        } else if (jsonData.settings.settings) { // Correct old object with bad naming #compatibility
                            Maco.localStorageSet('data', encodeURIComponent(JSON.stringify(jsonData.settings, replacer)));
                        } else if (jsonData.settings) { // Wrong even older object, old way of storing in local storage #compatibility
                            Maco.localStorageSet('data', encodeURIComponent(JSON.stringify(jsonData, replacer)));
                        }*/

                        if (jsonData.wardrobe) {
                            localStorage.setItem('TWCalc_Wardrobe', JSON.stringify(jsonData.wardrobe));
                        }

                        resolve(true);
                    } catch (e) {
                        console.error('Error parsing JSON file:', e.stack);
                        reject(new Error('Error parsing JSON file'));
                    }
                };

                reader.readAsText(file);
            };

            input.click();
        });
    };
    Maco.runDailyQuests = function() {
        function hasRequiredKeys(obj) { //#compatibility
            if (!obj || typeof obj !== 'object') return false; // Prevent null/undefined or non-object
            const REQUIRED_KEYS = ["id", "title", "requirements", "finish", "accept"];
            return REQUIRED_KEYS.every(key => key in obj);
        }
        Ajax.remoteCall('quest_employer', '', {
            employer: "paper",
            x: undefined,
            y: undefined
        }, function(json) {
            if (json.error) {
                new UserMessage(json.error, UserMessage.TYPE_ERROR).show();
                return;
            }

            const actions = [];
            const quests = json.employer.open;
            const disabledQuests = [2043364,2043368,2043365,2043369,2043367,2043371,2043366,2043370];
            if (!Array.isArray(quests)) return;

            if (!Array.isArray(Maco.dailyQuests.quests) || !hasRequiredKeys(Maco.dailyQuests.quests?.[0])) {
                Maco.dailyQuests.quests = [];
            }

            for (const quest of quests) {
                const { id, soloTitle, accepted, acceptable, finishable, requirements } = quest;
                const allSolved = requirements.every(req => req.solved === true);

                let existingQuest = Maco.dailyQuests.quests.find(q => q.id === id);
                // Build requirements info string
                let requirementsInfo = '';
                if (requirements.length === 1) {
                    requirementsInfo = requirements[0].info || '';
                } else if (requirements.length > 1) {
                    const filteredRequirements = requirements.filter((req, index) => {
                        // If it's the first requirement and both helpicons and jsInfo are null, skip it
                        if (index === 0 && req.helpicons == null && req.jsInfo == null) {
                            return false;
                        }
                        return true;
                    });

                    requirementsInfo = filteredRequirements.map(req => req.info).join(', ');
                }
                // Add new quest to the list, mark finish by default
                if (!existingQuest) {
                    existingQuest = { id, title: soloTitle, requirements: requirementsInfo || '', finish: !disabledQuests.includes(id), accept: false };
                    Maco.dailyQuests.quests.push(existingQuest);
                } else {
                    existingQuest.requirements = requirementsInfo || '';
                }

                // If quest exists and finish is disabled, skip it
                if (!existingQuest.finish && existingQuest !== undefined) {
                    continue;
                }

                // Build actions respecting the rules
                if (accepted && allSolved && finishable) {
                    // Directly finish → mark with "directFinish"
                    actions.push(() => finishQuest(id).then(success => success ? "directFinish" : false));
                } else if (acceptable && allSolved) {
                    // First accept, then finish → only return true/false, no rerun marker
                    actions.push(async () => {
                        const isFinishable = await acceptQuest(id);
                        await wait(generateRandomNumber(750, 1250));
                        return finishQuest(id, isFinishable); // resolves true/false
                    });
                } else if (acceptable && !allSolved && existingQuest.accept) {
                    // Just accept → no finish
                    actions.push(() => acceptQuest(id).then(() => false));
                }
            }

            Maco.refreshTab("quests");

            // Async runner with delay
            (async function runActions() {
                let rerunNeeded = false;

                for (const action of actions) {
                    try {
                        const result = await action();
                        if (result === "directFinish") rerunNeeded = true;
                    } catch (e) {
                        console.error("[Maco] Quest action error:", e);
                    }
                    await wait(generateRandomNumber(1000, 2000));
                }

                if (rerunNeeded) {
                    Maco.runDailyQuests();
                }
            })();
        });

        function acceptQuest(quest_id) {
            return new Promise((resolve, reject) => {
                Ajax.remoteCall("quest", "accept_quest", {
                    quest_id: quest_id
                }, function(json) {
                    if (json.error) {
                        new UserMessage(json.msg, UserMessage.TYPE_ERROR).show();
                        reject(json.error);
                    } else {
                        EventHandler.signal('questemployer_changed', ['accepted', quest_id]);
                        const quest = QuestLog.getEmployerQuest(quest_id);
                        if (quest) {
                            quest.accepted = true;
                            quest.isChallenge = json.isChallenge;
                            quest.finishable = json.finishable;
                            quest.updateQuest();
                            QuestTrackerWindow.toggleTracking(quest, true);
                            QuestLog.addQuest(quest);
                        }
                        resolve(json.finishable);
                    }
                });
            });
        }

        function finishQuest(quest_id, finishable = true) {
            return new Promise(resolve => {
                if (!finishable) return resolve(false);

                Ajax.remoteCall("quest", "finish_quest", {
                    quest_id: quest_id,
                    reward_option_id: undefined
                }, function(json) {
                    if (json.health !== undefined)
                        EventHandler.signal("health", [json.health]);

                    if (json.error) {
                        new UserMessage(json.msg, UserMessage.TYPE_ERROR).show();
                        return resolve(false);
                    }

                    // Success path
                    Character.updateDailyTask('quests');
                    EventHandler.signal('questemployer_changed', ['finished', quest_id]);
                    var quest = QuestLog.getQuest(quest_id);
                    if (quest) {
                        quest.setGainedRewards(json.allRewards);
                        quest.questCompletionHint = json.questCompletionHint;
                        quest.questCompletionText = json.questCompletionText;
                        quest.updateQuest();
                        QuestLog.addSolvedQuest(quest);
                    }
                    QuestLog.removeQuest(quest_id, false);
                    if (json.reportData) {
                        ReportWindow.open(json.reportData.report_id, json.reportData.hash);
                    }
                    try {
                        $.globalEval(json.eval);
                    } catch (e) {
                        if (window.DEBUG) console.log("Evaluation failed: ", e);
                    }

                    resolve(true);
                });
            });
        }
    };
    Maco.getStatusIcon = function() {
        return [0, 4].includes(Maco.currentState)
            ? 'https://westsk.innogamescdn.com/images/chat/status_offline.png'
            : [3, 5, 6, 7].includes(Maco.currentState)
            ? 'https://westsk.innogamescdn.com/images/chat/status_idle.png'
            : 'https://westsk.innogamescdn.com/images/chat/status_online.png';
    };
    Maco.updateStatusIcon = function() {
        var imgSrc = Maco.getStatusIcon();
        $('.status-icon-container img').attr('src', imgSrc).attr('title', Maco.states[Maco.currentState]);
    };
    Maco.createWindow = function() {
        var macoWindow = wman.open("Maco").setResizeable(false).setMinSize(650, 480).setSize(650, 480).setMiniTitle("Maco");
        var content = $('<div class=\'Maco2window\'/>');

        var statusIconContainer = $('<div class="status-icon-container"></div>');
        var imgSrc = Maco.getStatusIcon();
        var statusIcon = $('<div class="player-state"><img src="' + imgSrc + '"></div>');
        statusIcon.css({
            position:'absolute', top:'-15.5px', left:'5.5px',
            margin:'0', 'padding-left':'5px', 'padding-right':'5px',
            border:'none', verticalAlign:'middle'
        });

        var version = $(`<p><b>v. ${Maco.version}</b></p>`).css({
            position:'absolute', top:'-13.5px', right:'9px',
            'padding-left':'10px', 'padding-right':'10px',
            transform:'scale(0.85)', 'user-select':'text'
        });

        $('<style>') // styles for flashing effect
            .prop('type', 'text/css')
            .html(`
                .flashing-red {
                    color: red;
                    cursor: pointer;
                    animation: flash-warning 1s infinite alternate;
                    position: absolute;
                    top: -15px;
                    left: 60px;
                }

                @keyframes flash-warning {
                    0% { opacity: 1; }
                    50% { opacity: 1; }
                    100% { opacity: 0.0; }
                }
            `)
            .appendTo('head');

        if (Player.hasLoginBonus) {
            var loginRewardWarningButton = $('<span>⚠ Login reward not collected!</span>')
                .addClass('flashing-red')
                .on('click', function() {
                    Maco.forceCollectLoginReward();
                    $(this).remove();
                });

            statusIconContainer.append(loginRewardWarningButton);
        }

        statusIconContainer.append(statusIcon);
        statusIconContainer.append(version);
        macoWindow.appendToContentPane(statusIconContainer);

        function tabContentControl(tab) {
            Maco.removeActiveTab();
            Maco.removeWindowContent();
            Maco.addActiveTab(tab);
        }

        const tabs = {
            "jobs":"Jobs",
            "addedJobs":"Added jobs",
            "sets":"Sets",
            "consumables":"Consumables",
            "stats":"Stats",
            "settings":"Settings",
            "favoriteJobs":"Worker",
            "quests":"Quests",
            "townBuild":"Builder",
            "notificationSettings":"Notifications"
        };

        var tabLogic = function(win, id) {
            var content = $('<div class=\'Maco2window\'/>');
            switch(id) {
                case "jobs":
                    Maco.loadJobsData(function(){
                        tabContentControl(id);
                        content.append(Maco.createJobsTab());
                        Maco.window.appendToContentPane(content);
                        Maco.addJobTableCss();
                        $(".Maco2window .tw2gui_scrollpane_clipper_contentpane").css({"top":Maco.jobsTablePosition.content});
                        $(".Maco2window .tw2gui_scrollbar_pulley").css({"top":Maco.jobsTablePosition.scrollbar});
                        Maco.addSortEventsHeader();
                        Maco.addJobFilterEvent();
                        $('#jobFilter_textfield').attr('autocomplete', 'off').trigger('focus');
                    });
                    break;
                case "addedJobs":
                    tabContentControl(id);
                    content.append(Maco.createAddedJobsTab());
                    Maco.window.appendToContentPane(content);
                    $(".Maco2window .tw2gui_scrollpane_clipper_contentpane").css({"top":Maco.addedJobsTablePosition.content});
                    $(".Maco2window .tw2gui_scrollbar_pulley").css({"top":Maco.addedJobsTablePosition.scrollbar});
                    Maco.addAddedJobsTableCss();
                    break;
                case "consumables":
                    tabContentControl(id);
                    Maco.findAllConsumables();
                    content.append(Maco.createConsumablesTab());
                    Maco.window.appendToContentPane(content);
                    $(".Maco2window .tw2gui_scrollpane_clipper_contentpane").css({"top":Maco.consumablesTablePosition.content});
                    $(".Maco2window .tw2gui_scrollbar_pulley").css({"top":Maco.consumablesTablePosition.scrollbar});
                    Maco.addConsumableTableCss();
                    break;
                case "sets":
                    Maco.loadSets(function() {
                        tabContentControl(id);
                        content.append(Maco.createSetGui())
                        Maco.window.appendToContentPane(content);
                    });
                    break;
                case "stats":
                    tabContentControl(id);
                    content.append(Maco.createStatisticsGui());
                    Maco.window.appendToContentPane(content);
                    break;
                case "settings":
                    tabContentControl(id);
                    content.append(Maco.createSettingsGui());
                    Maco.window.appendToContentPane(content);
                    break;
                case "favoriteJobs":
                    tabContentControl(id);
                    content.append(Maco.createFavoriteJobsTab());
                    Maco.window.appendToContentPane(content);
                    $(".Maco2window .tw2gui_scrollpane_clipper_contentpane").css({"top":Maco.favoriteJobsTablePosition.content});
                    $(".Maco2window .tw2gui_scrollbar_pulley").css({"top":Maco.favoriteJobsTablePosition.scrollbar});
                    Maco.addFavoriteJobsTableCss();
                    break;
                case "quests":
                    tabContentControl(id);
                    content.append(Maco.createQuestsTab());
                    Maco.window.appendToContentPane(content);
                    $(".Maco2window .tw2gui_scrollpane_clipper_contentpane").css({"top":Maco.questsTablePosition.content});
                    $(".Maco2window .tw2gui_scrollbar_pulley").css({"top":Maco.questsTablePosition.scrollbar});
                    Maco.addQuestsTableCss();
                    break;
                case "townBuild":
                    Maco.loadCityHall(function(data) {
                        tabContentControl(id);
                        content.append(Maco.createTownBuildGui(data));
                        Maco.window.appendToContentPane(content);
                    });
                    break;
                case "notificationSettings":
                    tabContentControl(id);
                    content.append(Maco.createNotificationsGui());
                    Maco.window.appendToContentPane(content);
                    break;
            }

            Maco.lastActiveTab = id;
        }

        for (var tab in tabs) {
            macoWindow.addTab(tabs[tab], tab, tabLogic);
        }

        Maco.window = macoWindow;
        Maco.selectTab(Maco.lastActiveTab);
    };
    Maco.refreshTab = function(key) {
        const activeTab = Maco.getActiveTab();
        const tabKey = key != undefined ? key : activeTab;
        if (tabKey && tabKey === activeTab) {
            Maco.window.tabIds[tabKey].f(Maco.window, tabKey);
        }
    };
    Maco.selectTab = function(key) {
        if (!Maco.window?.tabIds?.[key]) return;
        Maco.window?.tabIds[key].f(Maco.window, key);
    };
    Maco.removeActiveTab = function() {
        const activeTab = Maco.getActiveTab();
        if (['jobs', 'addedJobs', 'consumables', 'favoriteJobs'].includes(activeTab)) { // save scrollbar position before removing GUI
            Maco[activeTab + "TablePosition"].content = $(".Maco2window .tw2gui_scrollpane_clipper_contentpane").css("top");
            Maco[activeTab + "TablePosition"].scrollbar = $(".Maco2window .tw2gui_scrollbar_pulley").css("top");
        }
        $('div.tw2gui_window_tab', Maco.window.divMain).removeClass('tw2gui_window_tab_active');
    };
    Maco.addActiveTab = function(key) {
        $('div._tab_id_' + key, Maco.window.divMain).addClass('tw2gui_window_tab_active');
    };
    Maco.removeWindowContent = function() {
        $(".Maco2window").remove();
    };
    Maco.getActiveTab = function() {
        const activeTab = $('div.tw2gui_window_tab_active', Maco.window?.divMain);
        if (activeTab.length > 0) {
            var tabKey = activeTab.attr('class').match(/_tab_id_([^\s]+)/);
            if (tabKey && tabKey.length > 1) {
                return tabKey[1];
            }
        }
        return '';
    };
    Maco.addJobTableCss = function() {
        $(".Maco2window .row_head").css({"margin-top":"1px"});
        $(".Maco2window .dummy").css({"float": "left"});
        $(".Maco2window .jobIcon").css({"width":"70px"});
        $(".Maco2window .jobName").css({"width":"150px"});
        $(".Maco2window .jobXp").css({"width":"40px"});
        $(".Maco2window .jobMoney").css({"width":"40px"});
        $(".Maco2window .jobMotivation").css({"width":"40px"});
        $(".Maco2window .jobDistance").css({"width":"80px"});
        $(".Maco2window .jobAdd").css({"width":"111px"});
        $(".Maco2window .row .jobName").css({"width":"150px", "margin-bottom":"10px"});
        $(".Maco2window .row .jobXp").css({"width":"40px", "margin-bottom":"10px"});
        $(".Maco2window .row .jobMoney").css({"width":"40px", "margin-bottom":"10px"});
        $(".Maco2window .row .jobMotivation").css({"width":"40px", "margin-bottom":"10px"});
        $(".Maco2window .row .jobDistance").css({"width":"80px", "margin-bottom":"10px"});
        $(".Maco2window .row .jobAdd").css({"width":"111px", "margin-bottom":"5px"});
        $(".Maco2window .row .jobAddFavorite").css({"margin-bottom":"5px"});
        $(".Maco2window .row").css({"height":"55px", "background": "none"});
        $(".Maco2window .trows").css({"height":"360px"});
        $('.Maco2window').find('.fancytable').css('height', '380px');
        $('.Maco2window').find('.tbody').css('height', '290px');
        $('.Maco2window').find('.tw2gui_scrollpane').css('height', '290px');
        $('.Maco2window').find('.tfoot').css('height', '30px');
    };
    Maco.addAddedJobsTableCss = function() {
        //$(".Maco2window .row_head").css({"margin-bottom":"3.5px", "margin-top":"3px"});
        $(".Maco2window .jobIcon").css({"width":"70px"});
        $(".Maco2window .jobName").css({"width":"150px"});
        $(".Maco2window .jobStopMotivation").css({"width":"110px"});
        $(".Maco2window .jobSet").css({"width":"110px"});
        $(".Maco2window .jobRemove").css({"width":"91px"});
        $(".Maco2window .row .jobName").css({"width":"150px", "margin-bottom":"10px"});
        $(".Maco2window .row .jobStopMotivation").css({"width":"110px", "margin-bottom":"10px"});
        $(".Maco2window .row .jobSet").css({"width":"110px", "margin-bottom":"10px"});
        $(".Maco2window .row .jobRemove").css({"width":"91px", "margin-bottom":"5px"});
        $(".Maco2window .row .jobAddFavorite").css({"margin-bottom":"5px"});
        $(".Maco2window .row").css({"height":"55px", "background": "none"});
        $('.Maco2window').find('.tw2gui_scrollpane').css('height', '250px');
    };
    Maco.addFavoriteJobsTableCss = function() {
        //$(".Maco2window .row_head").css({"margin-bottom":"3.5px", "margin-top":"3px"});
        $(".Maco2window .dummy").css({"float": "left"});
        $(".Maco2window .jobIcon").css({"width":"70px"});
        $(".Maco2window .jobName").css({"width":"170px"});
        $(".Maco2window .jobSet").css({"width":"130px"});
        $(".Maco2window .jobRank").css({"width":"50px", "font-weight": "bold"});
        $(".Maco2window .jobMoveUp").css({"width":"28px"});
        $(".Maco2window .jobMoveDown").css({"width":"45px"});
        $(".Maco2window .row .jobRank").css({"padding-left":"2px"});
        $(".Maco2window .row .jobMoveUp").css({"height":"30px", "display": "flex", "align-items": "center"});
        $(".Maco2window .row .jobMoveDown").css({"height":"30px", "display": "flex", "align-items": "center"});
        $(".Maco2window .jobRemove").css({"width":"50px", "display": "flex", "align-items": "center"});
        $(".Maco2window .row:not(.row_head) > *:not(.jobIcon)").css({"margin-top": "4px"});
        $(".Maco2window .row").css({"background": "none", "height":"55px", "display": "flex", "align-items": "center"});
        $(".Maco2window .trows").css({"height":"360px"});
        $('.Maco2window').find('.fancytable').css('height', '380px');
        $('.Maco2window').find('.tbody').css('height', '295px');
        $('.Maco2window').find('.tw2gui_scrollpane').css('height', '295px');
        $('.Maco2window').find('.tfoot').css('height', '30px');
    };
    Maco.addQuestsTableCss = function() {
        $(".Maco2window .questTitle").css({"width":"190px"});
        $(".Maco2window .questRequirements").css({"width":"265px"});
        $(".Maco2window .questFinish").css({"width":"60px"});
        $(".Maco2window .questAccept").css({"width":"50px"});
        $(".Maco2window .row .cell_0").css({"margin-left":"5px"});
        $(".Maco2window .row").css({"display": "flex"});
        $(".Maco2window .row .questFinish").css({"display": "inline-flex", "align-items": "center"});
        $(".Maco2window .row .questAccept").css({"display": "inline-flex", "align-items": "center"});
        $('.Maco2window').find('.fancytable').css('height', '380px');
        $('.Maco2window').find('.tbody').css('height', '295px');
        $('.Maco2window').find('.tw2gui_scrollpane').css('height', '295px');
        $('.Maco2window').find('.tfoot').css('height', '30px');
    };
    Maco.addConsumableTableCss = function() {
        $(".Maco2window .consumIcon").css({"width":"65px"});
        //$(".Maco2window .consumIcon .item").css({"background":"none"});
        $(".Maco2window .consumName").css({"width":"130px"});
        $(".Maco2window .consumEnergy").css({"width":"70px"});
        $(".Maco2window .consumMotivation").css({"width":"70px"});
        $(".Maco2window .consumHealth").css({"width":"60px"});
        $(".Maco2window .consumBuffs").css({"width":"130px"});
        $(".Maco2window .row .consumSelected").css({"display": "flex", "align-items": "center"});
        $(".Maco2window .row:not(.row_head) > *:not(.consumIcon)").css({"margin-top": "5px"});
        $(".Maco2window .row").css({"height":"60px", "background-position":"center -28px", "display": "flex", "align-items": "center"});
        $('.Maco2window').find('.tw2gui_scrollpane').css('height', '250px');
    };
    Maco.addSortEventsHeader = function() {
        $(".Maco2window .jobXp").click(function() {
            (Maco.sortJobTable.xp === 0) ? Maco.sortJobTable.xp = 1 : Maco.sortJobTable.xp *= -1;
            Maco.sortJobTable.distance = 0;
            Maco.sortJobTable.money = 0;
            Maco.refreshTab("jobs");
        });
        $(".Maco2window .jobMoney").click(function() {
            (Maco.sortJobTable.money === 0) ? Maco.sortJobTable.money = 1 : Maco.sortJobTable.money *= -1;
            Maco.sortJobTable.distance = 0;
            Maco.sortJobTable.xp = 0;
            Maco.refreshTab("jobs");
        });
        $(".Maco2window .jobDistance").click(function() {
            (Maco.sortJobTable.distance === 0) ? Maco.sortJobTable.distance = -1 : Maco.sortJobTable.distance *= -1;
            Maco.sortJobTable.xp = 0;
            Maco.sortJobTable.money = 0;
            Maco.refreshTab("jobs");
        });
    };
    Maco.addJobFilterEvent = function() {
        var f = function () {
            if (Maco.filterTimeout != undefined) {
                clearTimeout(Maco.filterTimeout);
            }
            Maco.filterTimeout = setTimeout(function () {
                Maco.jobFilter.filterJob = $('#jobFilter_textfield').val() || "";
                $(".Maco2window .tw2gui_scrollpane_clipper_contentpane").css({"top":"0px"});
                $(".Maco2window .tw2gui_scrollbar_pulley").css({"top":"0px"});
                Maco.refreshTab("jobs");
            }, 700);
        };
        $('#jobFilter_textfield').on('keyup change', f);
    };
    Maco.createJobsTab = function() {
        var htmlSkel = $("<div id = \'jobs_overview'\></div>");
        var html = $("<div class = \'jobs_search_foot'\ style=\'position:relative; align-items: center; display: flex; justify-content: space-between;'\><div id=\'jobFilter'\style=\'margin-right: 25px;'\></div><div id=\'job_only_silver'\style=\'margin-right: 15px;'\></div><div id=\'job_no_silver'\style=\'margin-right: 10px;'\></div><div id=\'job_center'\style=\'margin-right: 10px;'\></div><div id=\'job_hide_favorites'\style=\' '\></div></div>");
        var xpIcon = '<img src="/images/icons/star.png">';
        var dollarIcon = '<img src="/images/icons/dollar.png">';
        var motivationIcon = '<img src="/images/icons/motivation.png">';
        var arrow_desc = '&nbsp;<img src="../images/window/jobs/sortarrow_desc.png"/>';
        var arrow_asc = '&nbsp;<img src="../images/window/jobs/sortarrow_asc.png"/>';

        var textfield = new west.gui.Textfield("jobFilter_textfield").setPlaceholder("Search job name").setWidth(140);
        if (Maco.jobFilter.filterJob) {
            textfield.setValue(Maco.jobFilter.filterJob);
        }
        var clearImage = $('<img/>', {src: '../images/chat/servicegrade_traitor.png',
            click: function () {
                $('#jobFilter_textfield').val('').trigger('change');
            },
            css: {filter: 'grayscale(100%)', '-webkit-filter': 'grayscale(100%)', '-moz-filter': 'grayscale(100%)', '-o-filter': 'grayscale(100%)', position: 'absolute', top: '7px', left: '135px'}
        });

        let uniqueJobs = [];
        if (!Maco.jobFilter.filterNoSilver) {
            if (!Maco.isDestinationReached(Maco.lastPosition) || Maco.uniqueJobs.length === 0) {
                Maco.uniqueJobs = Maco.getUniqueJobs(); // 12 ms
            }
            Maco.lastPosition = {...Character.position};
            uniqueJobs = Maco.filterUniqueJobs(Maco.uniqueJobs); // 16 ms
        } else {
            uniqueJobs = Maco.getAllFilteredUniqueJobs();
        }

        //const uniqueJobs = Maco.getAllFilteredUniqueJobs();
        const favoriteJobIds = new Set(Maco.favoriteJobs.map(job => job.id));
        const addedJobIds = new Set(Maco.addedJobs.map(job => job.id));

        var table = new west.gui.Table();
        table.addColumn("dummy","dummy").addColumn("jobIcon","jobIcon").addColumn("jobName","jobName").addColumn("jobXp","jobXp").addColumn("jobMoney","jobMoney").addColumn("jobMotivation","jobMotivation").addColumn("jobDistance","jobDistance").addColumn("jobAdd","jobAdd").addColumn("jobAddFavorite","jobAddFavorite");
        table.appendToCell("head","dummy","").appendToCell("head","jobIcon","Job icon").appendToCell("head","jobName","Job name").appendToCell("head","jobXp", xpIcon + (Maco.sortJobTable.xp == 1 ? arrow_asc : Maco.sortJobTable.xp == -1 ? arrow_desc : "")).appendToCell("head","jobMoney", dollarIcon + (Maco.sortJobTable.money == 1 ? arrow_asc : Maco.sortJobTable.money == -1 ? arrow_desc : "")).appendToCell("head","jobMotivation",motivationIcon).appendToCell("head","jobDistance","Distance " + (Maco.sortJobTable.distance == 1 ? arrow_asc : Maco.sortJobTable.distance == -1 ? arrow_desc : "")).appendToCell("head","jobAdd","").appendToCell("head","jobAddFavorite","Save");

        for (let job = 0; job < uniqueJobs.length; job++) {
            const isAdded = addedJobIds.has(uniqueJobs[job].id);
            table.appendRow()
                .appendToCell(-1, "jobIcon", Maco.getJobIcon(uniqueJobs[job].silver, uniqueJobs[job].id, uniqueJobs[job].x, uniqueJobs[job].y, true)) // 50ms
                .appendToCell(-1, "jobName", Maco.getJobName(uniqueJobs[job].id) + "&nbsp; ") // 25ms
                .appendToCell(-1, "jobXp", uniqueJobs[job].experience) // 15ms
                .appendToCell(-1, "jobMoney", uniqueJobs[job].money) // 15ms
                .appendToCell(-1, "jobMotivation", uniqueJobs[job].motivation) // 15ms
                .appendToCell(-1, "jobDistance", uniqueJobs[job].distance.formatDuration()) // 30 ms
                .appendToCell(-1, "jobAdd", Maco.createAddJobButton(uniqueJobs[job].x, uniqueJobs[job].y, uniqueJobs[job].id, isAdded, job)) // 60ms
                .appendToCell(-1, "jobAddFavorite", Maco.makeFavoriteJobCheckbox(uniqueJobs[job].id, Maco.jobsTablePosition, favoriteJobIds)) // 70ms
                .getRow().css("opacity", isAdded ? 0.6 : 1);
        }

        let refreshDeferred = false;
        function deferRefresh() {
            if (refreshDeferred) return;
            refreshDeferred = true;
            setTimeout(function() {
                refreshDeferred = false;
                Maco.debouncedSaveAll(3000);
                $(".Maco2window .tw2gui_scrollpane_clipper_contentpane").css({"top":"0px"});
                $(".Maco2window .tw2gui_scrollbar_pulley").css({"top":"0px"});
                Maco.selectTab("jobs");
            }, 0);
        }

        var checkboxOnlySilver = new west.gui.Checkbox()
            .setLabel("Silvers")
            .setSelected(Maco.jobFilter.filterOnlySilver)
            .setCallback(function() {
                if (this.isSelected()) {
                    Maco.jobFilter.filterOnlySilver = this.isSelected();
                    checkboxNoSilver.setSelected(!this.isSelected());
                } else {
                    Maco.jobFilter.filterOnlySilver = false;
                }
                deferRefresh();
            });

        var checkboxNoSilver = new west.gui.Checkbox()
            .setLabel("No silvers")
            .setSelected(Maco.jobFilter.filterNoSilver)
            .setCallback(function() {
                if (this.isSelected()) {
                    Maco.jobFilter.filterNoSilver = this.isSelected();
                    checkboxOnlySilver.setSelected(!this.isSelected());
                } else {
                    Maco.jobFilter.filterNoSilver = false;
                }
                deferRefresh();
            });

        var checkboxCenterJobs = new west.gui.Checkbox()
            .setLabel("Center jobs")
            .setSelected(Maco.jobFilter.filterCenterJobs)
            .setCallback(function() {
                Maco.jobFilter.filterCenterJobs = this.isSelected();
                deferRefresh();
            });

        var checkboxHideFavorites = new west.gui.Checkbox()
            .setLabel("Hide saved")
            .setSelected(Maco.jobFilter.filterFavorites)
            .setCallback(function() {
                Maco.jobFilter.filterFavorites = this.isSelected();
                deferRefresh();
            });

        var checkboxEnoughLP = new west.gui.Checkbox()
            .setLabel("Unlocked")
            .setSelected(Maco.jobFilter.filterEnoughLP)
            .setCallback(function() {
                Maco.jobFilter.filterEnoughLP = this.isSelected();
                deferRefresh();
            });

        $('#jobFilter', html).append(textfield.getMainDiv());
        $('#jobFilter', html).append(clearImage);
        $("#job_only_silver",html).append(checkboxOnlySilver.getMainDiv());
        $("#job_no_silver",html).append(checkboxNoSilver.getMainDiv());
        $("#job_center",html).append(checkboxCenterJobs.getMainDiv());
        $("#job_hide_favorites",html).append(checkboxEnoughLP.getMainDiv());
        //$("#job_hide_favorites",html).append(checkboxHideFavorites.getMainDiv());
        table.appendToFooter("dummy", html);
        htmlSkel.append(table.getMainDiv());
        return htmlSkel;
    };
    Maco.createAddJobButton = function(x, y, id, isAdded, tableIndex) {
        var buttonAdd = new west.gui.Button("Add new job", function() {
            Maco.addJob(x,y,id);
            Maco.jobsTablePosition.content = $(".Maco2window .tw2gui_scrollpane_clipper_contentpane").css("top");
            Maco.jobsTablePosition.scrollbar = $(".Maco2window .tw2gui_scrollbar_pulley").css("top");
            Maco.debouncedSaveAll(3000);
            $(buttonAdd.getMainDiv()).hide();
            $(`#jobs_overview .row.row_${tableIndex}`).css("opacity", "0.6");
        });
        buttonAdd.setWidth(100);
        var buttonDiv = $(buttonAdd.getMainDiv()); // Wrap in jQuery
        return isAdded ? buttonDiv.css("display", "none") : buttonDiv;
    };
    Maco.makeFavoriteJobCheckbox = function(id, position, favoriteJobIds) {
        const checkbox = new west.gui.Checkbox()
            .setSelected(favoriteJobIds.has(id)) // Use Set for constant-time check
            .setId(id)
            .setCallback(function() {
                Maco.updateFavoriteJobs(parseInt(this.divMain.attr("id")), this.isSelected());
                Maco.debouncedSaveAll(3000);
            });
        return checkbox.getMainDiv();
    };
    Maco.setCheck = function() {
        const predefinedSets = [
            Maco.travelSet,
            Maco.jobSet,
            Maco.healthSet,
            Maco.regenerationSet,
            Maco.settings.fortBattle.attackSet,
            Maco.settings.fortBattle.defSet
        ];

        // Check if all predefined sets are defined in Maco.sets
        const arePredefinedSetsDefined = predefinedSets.every(setId => Maco.sets.has(setId) || setId <= -1 || Maco.wardrobe.has(setId));

        // Check if all sets for jobs in Maco.addedJobs are defined in Maco.sets
        const areJobSetsDefined = Maco.addedJobs.every(job => Maco.sets.has(job.set) || job.set <= -1 || Maco.wardrobe.has(job.set));

        return arePredefinedSetsDefined && areJobSetsDefined;
    };
    Maco.setsAssigned = function() {
        for (let i = 0; i < Maco.addedJobs.length; i++) {
            if (Maco.addedJobs[i].set <= -1) {
                return false
            }
        }
        return true;
    };
    Maco.startFlagCheck = function() {
        flagCheckInterval = setInterval(function() {
            if (!isQueueInProgress && !runJob_running && !walkToJob_running && !isRequestInProgress && !useConsumable_running) {
                executeQueuedActions();
                clearInterval(flagCheckInterval);
            }
        }, interval_long);
    };
    Maco.handleScriptStart = function(startDelay = 0) {
        if (!Maco.isRunning) Maco.currentState = 4;
        (Maco.addedJobs.length <= MAX_ALLOWED_JOBS) ? Maco.makeRoute() : Maco.createRoute();
        Maco.selectTab("addedJobs");
        Maco.debouncedSaveAll(1000);

        if (!Maco.isRunning && !isQueueInProgress && queuedActions.length === 0) {
            queuedActions.push(function() {
                Maco.isRunning = true;
                Maco.maxAllowedEnergy = 100;
                Maco.addRunTimeEventListeners();
                if (Maco.farmingAssistant.awaitNextSession) {
                    Maco.awaitNextSession();
                } else {
                    clearTimeout(startStopDelayTimeoutId);
                    startStopDelayTimeoutId = setTimeout(() => {
                        //if (Config.get("gui.animations")) {
                            Maco.startAnimationRemoveObserver();
                        //}
                        if (Maco.settings.autoReload) {
                            Maco.startReloadObserver();
                        }
                        Maco.startTime = new Date();
                        EventHandler.unlisten('handle_maco_start', Maco._onStart);
                        EventHandler.unlisten('handle_maco_stop', Maco._onStop);
                        EventHandler.listen('handle_maco_stop', Maco._onStop);
                        Maco.keepAlive.start();
                        startStopDelayTimeoutId = null;
                        if (Maco.canAttendBattle()) {
                            Maco.attendFortBattle();
                        } else {
                            Maco.run();
                        }
                    }, startDelay);
                }
            });

            Maco.startFlagCheck();
        }
    };
    Maco.handleButtonStopClick = function(stopDelay = 0) {
        clearTimeout(startStopDelayTimeoutId);
        clearInterval(flagCheckInterval);
        queuedActions = [];
        if (stopDelay > 0) {
            startStopDelayTimeoutId = setTimeout(() => {
                Maco.stopCleanup();
                waitForCondition(
                    () => (TaskQueue.queue.length === 0 && !runJob_running && !walkToJob_running && !useConsumable_running),
                    () => Maco.sleep({ dontWakeUp: true, message: "Scheduled stop." }),
                    500,
                    10000
                );
            }, stopDelay);
            Maco.refreshTab("addedJobs");
            return startStopDelayTimeoutId;
        } else {
            Maco.stopCleanup();
            waitForCondition(
                () => (TaskQueue.queue.length === 0 && !runJob_running && !walkToJob_running && !useConsumable_running),
                () => EventHandler.signal("maco_stopped"),
                500,
                5000,
                true
            );
        }
        return null;
    };
    Maco.stopCleanup = function() {
        Maco.currentState = 0;
        Maco.isRunning = false;
        Maco.keepAlive.stop();
        startStopDelayTimeoutId = null;
        clearInterval(reloadObserverInterval);
        Maco.removeRunTimeEventListeners();
        if (queueAnimationObserver != null) {
            queueAnimationObserver.disconnect();
            queueAnimationObserver = null;
        }
        Maco.selectTab("addedJobs");
        EventHandler.unlisten('handle_maco_stop', Maco._onStop);
        EventHandler.unlisten('handle_maco_start', Maco._onStart);
        EventHandler.listen('handle_maco_start', Maco._onStart);
    };
    Maco.finishRun = function(optMessage = "") {
        const message = "Finished. " + optMessage;
        Maco.stopCleanup();
        Maco.showNotification("The West - Script has stopped", message, "stopped");
    };
    Maco._onStart = function() {
        Maco.handleScriptStart();
        return EventHandler.ONE_TIME_EVENT;
    };
    Maco._onStop = function() {
        if (![5].includes(Maco.currentState)) {
            Maco.handleButtonStopClick(10 * 1000);
        }
        return EventHandler.ONE_TIME_EVENT;
    };
    Maco.awaitNextSession = async function() {
        Maco.currentState = 6;
        clearInterval(reloadObserverInterval);
        const intervalId = setInterval(() => {
            if (!Maco.isRunning || Maco.currentState !== 6 || !Maco.farmingAssistant.awaitNextSession) {
                clearInterval(intervalId);
            } else if (Maco.isSessionExpired()) {
                clearInterval(intervalId);
                Maco.saveAll();
                Maco.reload("Awaited session started. ");
            }
        }, 10000);
    };
    Maco.createAddedJobsTab = function() {
        var htmlSkel = $("<div id=\'added_jobs_overview'\></div>");
        var footerHtml = $("<div id=\'start_Maco'\ style=\'position:relative;'\><span class =\'Maco_state'\ style=\' position:absolute; left:20px; top:8px; font-family: Arial, Helvetica, sans-serif; font-size: 15px; font-weight: bold;'\> Current state: "+ Maco.states[Maco.currentState] +"</span><div class=\'Maco_skip_tutorial'\ style=\'position:absolute; left:20px; top:43px;'\></div><div class=\'Maco_run'\ style=\'position:absolute; left:310px; top:20px;'\></div></div>");
        if (Maco.addedJobsChanged() && Maco.addedJobs.length > 2 && Maco.isRunning) {
            var routeWarning = $("<div class='route_warning' style='position:absolute; left:20px; top:40px; font-family: Arial, Helvetica, sans-serif; font-size: 13px; font-weight: bold;'>Jobs changed! (Press 'Recalc' to recalculate route).</div>");
            footerHtml.append(routeWarning);
        }

        const favoriteJobIds = new Set(Maco.favoriteJobs.map(job => job.id));
        let activeJobIndex = null; // Track the currently active job index
        let scrollCheckInterval = null;
        var previousScrollTop = $(".Maco2window .tw2gui_scrollbar_pulley").css("top"); // Initialize previous scrollbar pulley position
        var buttonDiv = $("<div></div>").attr('title', Maco.explainerTranslations[Maco.translationLang].explainer_15);

        var buttonSaveCurrentGear = new west.gui.Button("Save current gear", function() {
            const jobIndex = buttonSaveCurrentGear.jobIndex; // retrieve the stored job index
            if (jobIndex !== undefined && Maco.addedJobs[jobIndex]) {
                Maco.saveCurrentGear(Maco.addedJobs[jobIndex].id);
                new UserMessage("Current gear saved.", UserMessage.TYPE_SUCCESS).show();
                Maco.debouncedSaveAll(1000);
                buttonDiv.hide();
                activeJobIndex = null;
                clearInterval(scrollCheckInterval);
            }
        });

        var buttonDeleteSavedGear = document.createElement("button");
        buttonDeleteSavedGear.style.cssText = "margin-left: 8px; transform: scale(1.1); transformOrigin: center; width: 16px; height: 19px; background: url('https://westsk.innogamescdn.com/images/window/messages/icons.png?2') repeat scroll 0 0 transparent; background-position: -292px -4px; padding: 0; border: none; outline: none; display: inline-block; cursor: pointer; user-select: none; font-size: 13px; white-space: nowrap; line-height: 29px;";
        buttonDeleteSavedGear.addEventListener("click", function() {
            const jobIndex = buttonSaveCurrentGear.jobIndex; // retrieve the stored job index
            if (jobIndex !== undefined && Maco.addedJobs[jobIndex]) {
                Maco.deleteSavedGear(Maco.addedJobs[jobIndex].id); 
                new UserMessage("Default best gear.", UserMessage.TYPE_SUCCESS).show();
                Maco.debouncedSaveAll(1000);
                buttonDiv.hide();
                activeJobIndex = null;
                clearInterval(scrollCheckInterval);
            }
        });

        buttonDiv.append(buttonSaveCurrentGear.getMainDiv());
        buttonDiv.append(buttonDeleteSavedGear);
        buttonDiv.hide(); // Initially hide the button

        function checkForScroll() { // Function to check for scroll events
            var currentScrollTop = $(".Maco2window .tw2gui_scrollbar_pulley").css("top");

            if (currentScrollTop !== previousScrollTop) {
                buttonDiv.hide();
                activeJobIndex = null;
                clearInterval(scrollCheckInterval);

                // Update previousScrollTop to current position
                previousScrollTop = currentScrollTop;
            }
        }
        function startScrollCheckInterval() {
            previousScrollTop = $(".Maco2window .tw2gui_scrollbar_pulley").css("top");
            scrollCheckInterval = setInterval(checkForScroll, 100);
        }

        var table = new west.gui.Table();
        table.addColumn("jobIcon","jobIcon").addColumn("jobName","jobName").addColumn("jobStopMotivation","jobStopMotivation").addColumn("jobSet","jobSet").addColumn("jobRemove","jobRemove").addColumn("jobAddFavorite","jobAddFavorite");
        table.appendToCell("head","jobIcon","Job icon").appendToCell("head","jobName","Job name").appendToCell("head","jobStopMotivation","Stop motivation").appendToCell("head","jobSet","Job set").appendToCell("head","jobRemove","").appendToCell("head","jobAddFavorite","Save");

        for (var jobIdx = 0; jobIdx < Maco.addedJobs.length; jobIdx++) {
            const jobId = Maco.addedJobs[jobIdx].id;
            const jobNameCell = $("<span>").html(Maco.getJobName(jobId) + "&nbsp; ");

            if (Maco.addedJobs.length > 1) {
                jobNameCell.css("cursor", "pointer").attr("title", "Save current gear");
                (function(index) { // Wrap this part to capture jobIdx
                    jobNameCell.on('click', function() { // Add click event listener to jobName to show/hide the buttonSaveCurrentGear
                        if (activeJobIndex === index) { // if the same job is clicked again, hide the button
                            buttonDiv.hide();
                            activeJobIndex = null;
                            clearInterval(scrollCheckInterval);
                        } else {
                            // Positioning and showing button logic
                            var clickedElement = $(this);
                            var parentOffset = clickedElement.closest(table.getMainDiv()).offset(); // closest parent offset
                            var position = clickedElement.offset(); // get the position of the clicked jobName
                            var topPosition = position.top - parentOffset.top + clickedElement.outerHeight() + 2; // add some padding
                            var leftPosition = position.left - parentOffset.left;

                            if (Maco.isGearSaved(Maco.addedJobs[index].id)) {
                                buttonDeleteSavedGear.style.display = 'inline-block';
                            } else {
                                buttonDeleteSavedGear.style.display = 'none';
                            }

                            buttonDiv.css({
                                transform: 'scale(0.9)',
                                transformOrigin: 'left',
                                position: 'absolute',
                                display: 'inline-flex',
                                'align-items': 'center',
                                top: topPosition + 'px', // position the button slightly below the clicked element
                                left: leftPosition + 'px'
                            }).show(); // show the button

                            buttonSaveCurrentGear.jobIndex = index; // store the job index
                            activeJobIndex = index; // set the current active job index
                            clearInterval(scrollCheckInterval);
                            startScrollCheckInterval();
                        }
                    });
                })(jobIdx); // Capture jobIdx
            }

            table.appendRow()
                .appendToCell(-1, "jobIcon", Maco.getJobIcon(Maco.addedJobs[jobIdx].silver, jobId, Maco.addedJobs[jobIdx].x, Maco.addedJobs[jobIdx].y))
                .appendToCell(-1, "jobName", jobNameCell)
                .appendToCell(-1, "jobStopMotivation", Maco.createMinMotivationTextfield(Maco.addedJobs[jobIdx].x, Maco.addedJobs[jobIdx].y, jobId, Maco.addedJobs[jobIdx].stopMotivation))
                .appendToCell(-1, "jobSet", Maco.createComboxJobSets(Maco.addedJobs[jobIdx].x, Maco.addedJobs[jobIdx].y, jobId))
                .appendToCell(-1, "jobRemove", Maco.createRemoveJobButton(Maco.addedJobs[jobIdx].x, Maco.addedJobs[jobIdx].y, jobId))
                .appendToCell(-1, "jobAddFavorite", Maco.makeFavoriteJobCheckbox(jobId, Maco.addedJobsTablePosition, favoriteJobIds));
        }

        // Hide buttonSaveCurrentGear when clicking elsewhere on the document
        $(document).on('click', function(event) {
            if (!$(event.target).closest(buttonDiv).length && 
                !$(event.target).closest("span").length) { // Ensure the click is not on the jobName or the button itself
                buttonDiv.hide();
                activeJobIndex = null; // Reset active job index when clicking outside
                clearInterval(scrollCheckInterval);
            }
        });

        let startDelay = 0,
            stopDelay = 0; // minutes

        const buttonStart = new west.gui.Button(Maco.addedJobs.length === 0 ? "Run saved jobs" : (Maco.currentState !== 0) ? "Recalc" : "Start", function() {
            if (!Maco.parseStopMotivation()) {
                new UserMessage("Wrong format of set stop motivation", UserMessage.TYPE_ERROR).show();
                return;
            }
            if (Maco.addedJobs.length === 0 && !Maco.swapSilverJobs()) {
                new UserMessage("No jobs to run.", UserMessage.TYPE_ERROR).show();
                return;
            }
            /*if (Maco.searchKeys[Maco.language] == undefined) {
                Maco.showAlert("Script is not supported for your server language.. it will not work properly.", false);
            }*/
            if (!Maco.setsAssigned()) {
                new UserMessage("Job set not assigned!", UserMessage.TYPE_ERROR).show();
            }
            if (!Maco.setCheck()) {
                Maco.showAlert(Maco.alertTranslations[Maco.translationLang].alert_2(0));
            }

            Maco.handleScriptStart(startDelay);
        });

        const buttonStop = new west.gui.Button((startStopDelayTimeoutId != null && Maco.currentState !== 4) ? "Stopping" : "Stop", function() {
            Maco.handleButtonStopClick(stopDelay);
        });
        (Maco.isRunning || Maco.currentState !== 0) ? buttonStop.enable() : buttonStop.disable();

        const startDelayDiv = Maco.createDelayInput({
            label: "start",
            initialValue: 0,
            onChange: (value) => {
                startDelay = Math.max(0, Number(value) || 0); // Update external startDelay variable
            },
            explainer: Maco.explainerTranslations[Maco.translationLang].explainer_25,
        });

        const stopDelayDiv = Maco.createDelayInput({
            label: "stop",
            initialValue: 0,
            onChange: (value) => {
                stopDelay = Math.max(0, Number(value) || 0); // Update external stopDelay variable
            },
            explainer: Maco.explainerTranslations[Maco.translationLang].explainer_25,
        });

        const delayDiv = (Maco.currentState === 0) ? startDelayDiv : stopDelayDiv;
        if (Maco.addedJobs.length === 1) {
            htmlSkel = Maco.addFarmingAssistantWiew(htmlSkel);
        }
        if ((characterId === 0 || LinearQuestHandler.hasTutorialQuest())) {
            $(".Maco_skip_tutorial", footerHtml).append(Maco.createSkipTutorialDiv());
        }
        htmlSkel.append(table.getMainDiv());
        htmlSkel.append(buttonDiv);
        $(".Maco_run", footerHtml).append(delayDiv);
        $(".Maco_run", footerHtml).append(buttonStart.getMainDiv());
        $(".Maco_run", footerHtml).append(buttonStop.getMainDiv());
        htmlSkel.append(footerHtml);
        return htmlSkel;
    };
    Maco.createDelayInput = function({ label, initialValue, onChange, explainer }) {
        let delayValue = initialValue; // Delay value in minutes
        const displayText = Maco.currentState !== 4 ? delayValue : " ";

        const delaySpan = $("<span>")
            .addClass(`${label}DelaySpan`)
            .css("font-weight", "bold")
            .text(displayText);

        const delayInput = $("<input>")
            .addClass(`${label}DelayInput`)
            .attr("type", "text")
            .val(delayValue)
            .hide();

        const delayDiv = $("<div>")
            .css({ display: "inline-block", cursor: "pointer", minWidth: "40px", maxWidth: "40px" })
            .attr("title", explainer)
            .append(delaySpan)
            .append(delayInput);

        // Event listeners
        delayDiv.on("click", function (event) {
            event.stopPropagation();
            delaySpan.hide();
            delayInput.show().css({ background: "inherit", border: "none", width: "38px" }).focus().select();
        });

        delayInput.on("blur focusout", function handleOnce() {
            handleDelay.call(this);
            delayInput.off("blur focusout", handleOnce); // Remove the listener
            setTimeout(() => {
                delayInput.one("blur focusout", handleOnce); // Reattach after execution
            }, 0); // Delay to reattach after the event completes
        });

        delayInput.on("keydown", function (event) {
            if (event.key === 'Enter') {
                $(this).trigger('blur');
            }
        });

        function handleDelay() {
            const inputValue = parseInt($(this).val());
            if (!isNaN(inputValue) && inputValue >= 0) {
                delayValue = inputValue * 60000; // Convert to milliseconds
                delaySpan.text(inputValue);
                onChange(delayValue); // Call the callback to update external state
            } else {
                $(this).val(0);
            }
            $(this).hide();
            delaySpan.show();
        }

        return delayDiv;
    };
    Maco.createMinMotivationTextfield = function(x, y, id, placeholder) {
        var componentId = "x-" + x + "y-" + y + "id-" + id;
        var textfield = new west.gui.Textfield().setId(componentId).onlyNumeric().setWidth(40).setValue(placeholder);
        //return textfield.getMainDiv();

        // Get the DOM element of the textfield's input
        var textfieldDiv = textfield.getMainDiv();
        textfieldDiv.attr('title', Maco.explainerTranslations[Maco.translationLang].explainer_17);
        var inputElement = textfieldDiv.find('input');

        // Attach the input event listener to detect changes
        inputElement.on('change', function() {
            Maco.parseStopMotivation(); //console.log("The new text field value is: " + inputElement.val());
            Maco.debouncedSaveAll(1000);
        });

        return textfieldDiv;
    };
    Maco.skipTutorial = function() {
        LinearQuestHandler.hasTutorialQuest = () => false;
        GameMap.Component.TutorialCloud = () => {};
        $('[id^="linear_quest"]').remove();
        EventHandler.signal("tutorial_finished");
        GameMap.refresh();
    };
    Maco.createSkipTutorialDiv = function() {
        var skipTutorialDiv = $("<div id='farmingAssistant_tutorialSkip'></div>");//.css({'position': 'absolute', 'top': '100px', 'left': '280px', 'z-index': '9999'});
        var checkboxSkipTutorial = new west.gui.Checkbox()
            .setLabel("Skip tutorial")
            .setSelected(Maco.settings.skipTutorial)
            .setCallback(function() {
                Maco.settings.skipTutorial = this.isSelected();
                Maco.debouncedSaveAll(100, () => new UserMessage("Saved successfully.", UserMessage.TYPE_SUCCESS).show());
                new UserMessage("Saved successfully.", UserMessage.TYPE_SUCCESS).show();
                if (this.isSelected() && LinearQuestHandler.hasTutorialQuest()) {
                    Maco.skipTutorial();
                }
            });
        skipTutorialDiv.append(checkboxSkipTutorial.getMainDiv());

        return skipTutorialDiv;
    };
    Maco.addFarmingAssistantWiew = function(htmlSkel) {
        var checkboxAssistantDiv = $("<div id='farmingAssistant_checkbox'></div>");
        checkboxAssistantDiv.attr('title', Maco.explainerTranslations[Maco.translationLang].explainer_24);
        var checkboxFarmingAssistant = new west.gui.Checkbox()
            .setLabel("Enable farming assistant")
            .setSelected(Maco.farmingAssistant.enabled)
            .setCallback(function() {
                Maco.farmingAssistant.enabled = this.isSelected();
                Maco.debouncedSaveAll(3000);
                if (Maco.farmingAssistant.enabled) {
                    $("#farmingAssistant_options").css('visibility', 'visible');
                } else {
                    $("#farmingAssistant_options").css('visibility', 'hidden');
                    Maco.farmingAssistant.stopLevel = false;
                    Maco.farmingAssistant.awaitNextSession = false;
                    Maco.refreshTab("addedJobs");
                }
            });
        checkboxAssistantDiv.append(checkboxFarmingAssistant.getMainDiv());
        $(checkboxAssistantDiv).css({
            'position': 'absolute', 'top': '100px', 'left': '80px',
            'z-index': '9999'
        });

        let comboboxGearLevel = new west.gui.Combobox("combobox_gear_level");
        const jobGear = Maco.jobsFarmingGear.find(item => item.jobid === Maco.addedJobs[0].id);
        if (jobGear && jobGear.hasOwnProperty(`level_0`)) {
            comboboxGearLevel.addItem(0, "Default" + "&nbsp;&nbsp;&nbsp;" + "\u2714");
        } else {
            comboboxGearLevel.addItem(0, "Default");
        }
        for (let i = 1; i < 10; i++) {
            if (jobGear && jobGear.hasOwnProperty(`level_${i}`)) {
                comboboxGearLevel.addItem(i, "Level " + i + "&nbsp;&nbsp;&nbsp;" + "\u2714");
            } else {
                comboboxGearLevel.addItem(i, "Level " + i);
            }
        }
        Maco.farmingAssistant.selectedGearLevel = (Character.level >= 1 && Character.level <= 9 && Maco.lastResult[Maco.currentJob.jobIdx] > 0) ? Character.level : Maco.farmingAssistant.selectedGearLevel;
        comboboxGearLevel = comboboxGearLevel.select(Maco.farmingAssistant.selectedGearLevel);
        comboboxGearLevel.addListener(function(value) {
            Maco.farmingAssistant.selectedGearLevel = value;
        });
        comboboxGearLevel.getMainDiv().attr('title', Maco.explainerTranslations[Maco.translationLang].explainer_22);

        var htmlSaveAssistantGear = $("<div></div>");
        htmlSaveAssistantGear.attr('title', Maco.explainerTranslations[Maco.translationLang].explainer_15);
        var buttonSaveAssistantGear = new west.gui.Button("Save current gear", function() {
            Maco.saveCurrentGear(Maco.addedJobs[0].id, Maco.farmingAssistant.selectedGearLevel);
            Maco.debouncedSaveAll(1000);
            new UserMessage("Current gear saved.", UserMessage.TYPE_SUCCESS).show();
            Maco.refreshTab("addedJobs");
        });

        var buttonDeleteAssistantGear = new west.gui.Button("Delete saved gear", function() {
            const deleted = Maco.deleteSavedGear(Maco.addedJobs[0].id, Maco.farmingAssistant.selectedGearLevel);
            if (deleted) {
                Maco.debouncedSaveAll(1000);
                new UserMessage("Gear deleted.", UserMessage.TYPE_SUCCESS).show();
                Maco.refreshTab("addedJobs");
            }
        });

        var buttonExportAssistantGear = new west.gui.Button("Export", function() {
            Maco.exportFarmingGear(Maco.addedJobs[0].id);
        });

        var buttonImportAssistantGear = new west.gui.Button("Import", function() {
            Maco.importFarmingGear()
                .then(() => {
                    Maco.saveAll();
                    new UserMessage("Gear imported successfully.", UserMessage.TYPE_SUCCESS).show();
                    Maco.refreshTab("addedJobs");
                })
                .catch(error => {
                    new UserMessage("Failed to import gear: " + error.message, UserMessage.TYPE_ERROR).show();
                });
        });

        var checkboxAwaitNextSession = new west.gui.Checkbox()
            .setLabel("Await jobs reset")
            .setSelected(Maco.farmingAssistant.awaitNextSession)
            .setCallback(function() {
                Maco.farmingAssistant.awaitNextSession = this.isSelected();
            });
        checkboxAwaitNextSession.getMainDiv().attr('title', Maco.explainerTranslations[Maco.translationLang].explainer_20);

        var checkboxAssistantStopLevel = new west.gui.Checkbox()
            .setLabel("Stop after: level up / jobs reset")
            .setSelected(Maco.farmingAssistant.stopLevel)
            .setCallback(function() {
                Maco.farmingAssistant.stopLevel = this.isSelected();
            });
        checkboxAssistantStopLevel.getMainDiv().attr('title', Maco.explainerTranslations[Maco.translationLang].explainer_21);

        var htmlFarmingAssistant = $("<div id='farmingAssistant_options'></div>");
        $(htmlFarmingAssistant).css({
            'visibility': (Maco.farmingAssistant.enabled) ? 'visible' : 'hidden',
            'position': 'absolute', 'width': '440px', 'top': '130px', 'left': '110px',
            'display': 'flex', 'flex-direction': 'column', 'align-items': 'flex-start',
            'z-index': '9999'
        });

        // Create a container for the first two elements with horizontal layout
        var topRow = $("<div></div>").css({
            'display': 'flex', 'width': '100%', 'justify-content': 'space-between', 'align-items': 'center', 'margin-top': '10px', 'margin-bottom': '10px'
        });
        htmlSaveAssistantGear.append(buttonSaveAssistantGear.getMainDiv());
        topRow.append(comboboxGearLevel.getMainDiv());
        topRow.append(htmlSaveAssistantGear);
        topRow.append(buttonDeleteAssistantGear.getMainDiv());

        var bottomRow = $("<div></div>").css({
            'display': 'flex', 'width': '100%', 'justify-content': 'space-around', 'align-items': 'center', 'margin-top': '10px', 'margin-bottom': '10px'
        });
        bottomRow.attr('title', Maco.explainerTranslations[Maco.translationLang].explainer_23);
        bottomRow.append(buttonImportAssistantGear.getMainDiv());
        bottomRow.append(buttonExportAssistantGear.getMainDiv());

        var smallSpace = $("<div></div>").css({'margin-bottom': '3px'});
        htmlFarmingAssistant.append(checkboxAwaitNextSession.getMainDiv());
        htmlFarmingAssistant.append(smallSpace);
        htmlFarmingAssistant.append(checkboxAssistantStopLevel.getMainDiv());
        htmlFarmingAssistant.append(topRow);
        htmlFarmingAssistant.append(bottomRow);

        htmlSkel.append(checkboxAssistantDiv);
        htmlSkel.append(htmlFarmingAssistant);
        return htmlSkel;
    };
    Maco.createQuestsTab = function() {
        var htmlSkel = $("<div id=\'quests_overview'\></div>");
        var footer = $('<div class="quests_options_foot" style="margin-left:5px;"><div id="daily_quests_options"></div></div>');
        var table = new west.gui.Table();
        table.addColumn("questTitle","questTitle").addColumn("questRequirements","questRequirements").addColumn("questFinish","questFinish").addColumn("questAccept","questAccept");
        table.appendToCell("head","questTitle","Quest Title").appendToCell("head","questRequirements","Requirements").appendToCell("head","questFinish","Finish").appendToCell("head","questAccept","Accept");

        for (let questIdx = 0; questIdx < Maco.dailyQuests.quests.length; questIdx++) {
            const questTitleCell = $("<span>").html(Maco.dailyQuests.quests[questIdx].title + "&nbsp; ");
            questTitleCell.css("cursor", "pointer").attr("title", Maco.dailyQuests.quests[questIdx].title);
            const questRequirementsCell = $("<span>").html(Maco.dailyQuests.quests[questIdx].requirements + "&nbsp; ");
            questRequirementsCell.css("cursor", "pointer").attr("title", Maco.dailyQuests.quests[questIdx].requirements);

            table.appendRow()
                .appendToCell(-1, "questTitle", questTitleCell)
                .appendToCell(-1, "questRequirements", questRequirementsCell)
                .appendToCell(-1, "questFinish", Maco.makeQuestCheckbox(Maco.dailyQuests.quests[questIdx], "finish"))
                .appendToCell(-1, "questAccept", Maco.makeQuestCheckbox(Maco.dailyQuests.quests[questIdx], "accept"))
        }

        var buttonRunQuests = new west.gui.Button("Run", function() {
            buttonRunQuests.disable();
            Maco.runDailyQuests();
        }).setWidth(60);

        var optionsContainerDiv = $("<div style='float: left; display: flex; align-items: center; gap:310px; width:max-content;'></div>");
        const checkboxEnableQuests = new west.gui.Checkbox()
            .setLabel("Enable Daily Quests")
            .setSelected(Maco.dailyQuests.enabled)
            .setCallback(function() {
                Maco.dailyQuests.enabled = this.isSelected();
                Maco.debouncedSaveAll(1000);
            });
        optionsContainerDiv.append(checkboxEnableQuests.getMainDiv());
        optionsContainerDiv.append(buttonRunQuests.getMainDiv());
        $("#daily_quests_options", footer).append(optionsContainerDiv);
        table.appendToFooter("questTitle", footer);
        htmlSkel.append(table.getMainDiv());
        return htmlSkel;
    };
    Maco.makeQuestCheckbox = function(quest, key) {
        const checkbox = new west.gui.Checkbox()
            .setSelected(quest[key])
            .setId(quest.id)
            .setCallback(function() {
                quest[key] = this.isSelected();
                Maco.debouncedSaveAll(1000);
            });
        return checkbox.getMainDiv();
    };
    Maco.createFavoriteJobsTab = function() {
        var htmlSkel = $("<div id=\'favoriteJobs_overview'\></div>");
        var footer = $('<div class="job_rank_select_foot" style="margin-left:5px;"><div id="max_rank_amount"></div></div>');

        const uniqueJobs = Maco.getAllUniqueJobs();
        // Precompute job indices for faster access
        const addedJobsMap = new Map(Maco.addedJobs.map((job, idx) => [job.id, idx]));
        const uniqueJobsMap = new Map(uniqueJobs.map((job, idx) => [job.id, { job: job, idx: idx }]));

        var table = new west.gui.Table();
        table.addColumn("dummy","dummy").addColumn("jobIcon","jobIcon").addColumn("jobName","jobName").addColumn("jobSet","jobSet").addColumn("jobRank","jobRank").addColumn("jobMoveUp","jobMoveUp").addColumn("jobMoveDown","jobMoveDown").addColumn("jobRemove","jobRemove");
        table.appendToCell("head","dummy","").appendToCell("head","jobIcon","Job icon").appendToCell("head","jobName","Job name").appendToCell("head","jobSet","Job set").appendToCell("head","jobRank","Rank").appendToCell("head","jobMoveUp","").appendToCell("head","jobMoveDown","").appendToCell("head","jobRemove","");

        for (let jobIdx = 0; jobIdx < Maco.favoriteJobs.length; jobIdx++) {
            const jobId = Maco.favoriteJobs[jobIdx].id;
            const addedJobIndex = addedJobsMap.get(jobId) ?? -1;
            const uniqueJobInfo = uniqueJobsMap.get(jobId);

            if (!uniqueJobInfo) {
                console.error("Job with ID " + jobId + " not found in Maco.createFavoriteJobsTab().");
                continue;
            }

            const currentJob = uniqueJobInfo.job;
            const jobNameCell = $("<span>").html(`${Maco.getJobName(jobId)}&nbsp; `);

            if (addedJobIndex === -1) {
                jobNameCell.css("cursor", "pointer").attr("title", "Add new job").on('click', function() {
                    Maco.addJob(currentJob.x, currentJob.y, currentJob.id);
                    Maco.favoriteJobsTablePosition.content = $(".Maco2window .tw2gui_scrollpane_clipper_contentpane").css("top");
                    Maco.favoriteJobsTablePosition.scrollbar = $(".Maco2window .tw2gui_scrollbar_pulley").css("top");
                    Maco.debouncedSaveAll(3000);
                    Maco.refreshTab("favoriteJobs");
                    new UserMessage("Job added.", UserMessage.TYPE_SUCCESS).show();
                });
            }

            var rankSpan = $("<span class='jobRank' style='cursor: pointer;'></span>").text(jobIdx + 1 + ".");
            var rankInput = $("<input type='number' class='jobRankInput'>").val(jobIdx + 1).hide();
            var rankCell = $("<td></td>").append(rankSpan).append(rankInput);

            table.appendRow()
                .appendToCell(-1, "jobIcon", Maco.getJobIcon(currentJob.silver, currentJob.id, currentJob.x, currentJob.y))
                .appendToCell(-1, "jobName", jobNameCell)
                .appendToCell(-1, "jobSet", Maco.createComboxFavoriteJobSets(jobIdx, addedJobIndex))
                .appendToCell(-1, "jobRank", rankCell)
                .appendToCell(-1, "jobMoveUp", Maco.createFavoriteJobShiftButton(jobIdx, 'up'))
                .appendToCell(-1, "jobMoveDown", Maco.createFavoriteJobShiftButton(jobIdx, 'down'))
                .appendToCell(-1, "jobRemove", Maco.createRemoveFavoriteJobButton(jobIdx));
        }

        var rankContainerDiv = $("<div style='float: left; display: flex; align-items: center;'></div>");
        var htmlMaxRank = $("<div></div>").css({'display': 'inline-block'});
        htmlMaxRank.attr('title', Maco.explainerTranslations[Maco.translationLang].explainer_13);
        //rankContainerDiv.append("<span style='font-weight: initial;'><b>Add all silver jobs up to rank:&nbsp; </b></span>");
        var maxRankTextField = new west.gui.Textfield("maxRank")
            .setWidth(40)
            .setValue(Maco.workerProfiles[Maco.workerProfiles.selected].maxJobRank)
            .onlyNumeric();
        htmlMaxRank.append("<span style='font-weight: initial;'><b>Add all silver jobs up to rank:&nbsp; </b></span>");
        htmlMaxRank.append(maxRankTextField.getMainDiv());
        rankContainerDiv.append(htmlMaxRank);
        //rankContainerDiv.append(maxRankTextField.getMainDiv());

        var htmlMaxJobs = $("<div style='display: inline-block; margin-left: 25px; margin-right: 25px;'></div>");
        htmlMaxJobs.attr('title', Maco.explainerTranslations[Maco.translationLang].explainer_14);
        htmlMaxJobs.append("<span style='font-weight: initial;'><b>Add more if less than: </b></span>");
        var maxJobsTextfiled = new west.gui.Textfield("maxJobs")
            .setWidth(30)
            .setValue(Maco.workerProfiles[Maco.workerProfiles.selected].jobsToAdd)
            .onlyNumeric();
        htmlMaxJobs.append(maxJobsTextfiled.getMainDiv());
        rankContainerDiv.append(htmlMaxJobs);

        var buttonSave = new west.gui.Button("Save", function() {
            if (isNumber(maxRankTextField.getValue())) {
                var rankVal = parseInt(maxRankTextField.getValue());
                Maco.workerProfiles[Maco.workerProfiles.selected].maxJobRank = Math.max(0, rankVal);
            }
            if (isNumber(maxJobsTextfiled.getValue())) {
                var jobsVal = parseInt(maxJobsTextfiled.getValue());
                Maco.workerProfiles[Maco.workerProfiles.selected].jobsToAdd = clamp(jobsVal, 0, MAX_ALLOWED_JOBS);
            }
            Maco.debouncedSaveAll(100, () => new UserMessage("Saved successfully.", UserMessage.TYPE_SUCCESS).show());
            Maco.selectTab("favoriteJobs");
        }).setWidth(60);

        if (Maco.favoriteJobs.length === 0) {
            function createJobsPresetButton(presetJobs, title) {
                return new west.gui.Button(title, function() {
                    loadJobsPreset(presetJobs, Maco.favoriteJobs);
                    Maco.debouncedSaveAll(100, () => new UserMessage("Loaded and Saved successfully.", UserMessage.TYPE_SUCCESS).show());
                    Maco.selectTab("favoriteJobs");
                }).setWidth(160);
            }
            var buttonLoadXPPreset = createJobsPresetButton(Maco.xpJobsPreset, "Load best XP jobs");
            var buttonLoadMoneyPreset = createJobsPresetButton(Maco.moneyJobsPreset, "Load best $ jobs");
            var comboboxDefaultJobSet = Maco.addComboboxSetItems(new west.gui.Combobox().setWidth(120), Maco.jobSet)
                .addListener(function(set) {
                    Maco.jobSet = set;
                });

            var workerPresetDiv = $("<div id='workerPreset_div'></div>").css({
                'position': 'absolute', 'top': '160px', 'left': '135px',
                'display': 'flex', 'flex-direction': 'column', 'align-items': 'center',
                'z-index': '9999'
            });
            var buttonsDiv = $("<div id='buttons_div'></div>").css({
                'display': 'flex', 'gap': '10px', 'justify-content': 'center'
            });
            var comboboxDiv = $("<div id='combobox_div'></div>").css({
                'margin-top': '15px', 'display': 'flex', 'gap': '10px', 'align-items': 'center', 'justify-content': 'center'
            });

            buttonsDiv.append(buttonLoadXPPreset.getMainDiv());
            buttonsDiv.append(buttonLoadMoneyPreset.getMainDiv());
            comboboxDiv.append($("<span>Default set: </span>"));
            comboboxDiv.append(comboboxDefaultJobSet.getMainDiv());
            workerPresetDiv.append(buttonsDiv);
            workerPresetDiv.append(comboboxDiv);

            htmlSkel.append(workerPresetDiv);
        }

        // Favorite jobs profiles
        let profileCheckboxes = {};

        let $profile1 = $('<input>', { type: 'checkbox', id: 'profile1', class: 'profile-checkbox' }).on("change", handleProfileChange);
        let $label1 = $('<label>', { for: 'profile1' }).append($profile1, ' Profile 1');
        profileCheckboxes.profile1 = $profile1;

        let $profile2 = $('<input>', { type: 'checkbox', id: 'profile2', class: 'profile-checkbox' }).on("change", handleProfileChange);
        let $label2 = $('<label>', { for: 'profile2' }).append($profile2, ' Profile 2');
        profileCheckboxes.profile2 = $profile2;

        let $workerProfilesDiv = $('<div id="profileContainer" style="display:flex; gap:15px; margin-left:15px;">').append($label1, $label2);
        profileCheckboxes[Maco.workerProfiles.selected]?.prop('checked', true);

        // Append everything
        rankContainerDiv.append(buttonSave.getMainDiv());
        $("#max_rank_amount", footer).append(rankContainerDiv);
        table.appendToFooter("dummy", footer);
        htmlSkel.append(table.getMainDiv());
        htmlSkel.append($workerProfilesDiv);

        // Rank focus logic
        htmlSkel.find('.jobRank').click(function() {
            var inputBox = $(this).find('.jobRankInput');
            inputBox.show().css({"background": "inherit", "border": "none", "width": "43px", "margin-left":"4px"}).focus();
            inputBox.select();
            $(this).find('.jobRank').hide();
        });

        // Use also focusout as an alternative to blur
        htmlSkel.find('.jobRankInput').one("blur focusout", function handleOnce() {
            handleJobRankInputBlur.call(this);
            setTimeout(() => {
                $(this).one("blur focusout", handleOnce); // Reattach after execution
            }, 0);
        });

        // Add keydown event to detect Enter key and trigger blur manually
        htmlSkel.find('.jobRankInput').on('keydown', function(event) {
            if (event.key === 'Enter') {
                $(this).trigger('blur');
            }
        });

        function handleJobRankInputBlur() {
            var rankValue = parseInt($(this).val());
            var currentIndex = $(this).closest('.row').index();

            if (!isNaN(rankValue) && rankValue > 0 && rankValue <= Maco.favoriteJobs.length) {
                var newIndex = rankValue - 1;
                var currentJob = Maco.favoriteJobs.splice(currentIndex, 1)[0];
                Maco.favoriteJobs.splice(newIndex, 0, currentJob);

                for (var i = 0; i < Maco.favoriteJobs.length; i++) {
                    $(this).closest('.Maco2window').find('.row').eq(i).find('.jobRank').text(i + 1 + ".");
                }

                Maco.favoriteJobsTablePosition.content = $(".Maco2window .tw2gui_scrollpane_clipper_contentpane").css("top");
                Maco.favoriteJobsTablePosition.scrollbar = $(".Maco2window .tw2gui_scrollbar_pulley").css("top");
                Maco.debouncedSaveAll(1000);
                Maco.selectTab("favoriteJobs");
            } else {
                $(this).val(currentIndex + 1); // If the input is invalid, revert to the current index
            }

            // Hide the input box and show the rank display again
            $(this).hide();
            $(this).siblings('.jobRank').show();
        }

        function handleProfileChange() {
            $(".profile-checkbox").not(this).prop("checked", false); // Uncheck the other checkbox
            Maco.workerProfiles.selected = this.checked ? this.id : "profile0";
            Maco.setWorkerProfile(Maco.workerProfiles.selected);
            $(".Maco2window .tw2gui_scrollpane_clipper_contentpane").css({"top":"0px"});
            $(".Maco2window .tw2gui_scrollbar_pulley").css({"top":"0px"});
            Maco.refreshTab("favoriteJobs");
            Maco.debouncedSaveAll(1000);
        }

        function loadJobsPreset(idArray, targetArray, set = Maco.jobSet) {
            idArray.forEach(id => targetArray.push({id: id, set: set}));
        }

        return htmlSkel;
    };
    Maco.createFavoriteJobShiftButton = function(jobIndex, direction) {
        var buttonShift = document.createElement("button");
        var rotateDeg = direction === 'up' ? '-90deg' : '90deg';
        var newIndex = direction === 'up' ? jobIndex - 1 : jobIndex + 1;
        if (direction === 'up') {
            buttonShift.style.cssText = "user-select: none; font-family: Arial, Verdana, sans-serif; font-size: 13px; width: 9px; height: 27px; background: url(https://westsk.innogamescdn.com/images/tw2gui/pagebar/arrows.png); background-position: -50px 8.5px; transform: rotate(" + rotateDeg + "); cursor: pointer; margin: 0; padding: 0; display: inline-block; border: none; outline: none;";
        } else {
            buttonShift.style.cssText = "user-select: none; font-family: Arial, Verdana, sans-serif; font-size: 13px; width: 9px; height: 27px; background: url(https://westsk.innogamescdn.com/images/tw2gui/pagebar/arrows.png); background-position: -50px 0px; transform: rotate(" + rotateDeg + "); cursor: pointer; margin: 0; padding: 0; display: inline-block; border: none; outline: none;";
        }
        buttonShift.addEventListener("click", function() {
            if (direction === 'up' && jobIndex > 0) {
                const temp = Maco.favoriteJobs[jobIndex];
                Maco.favoriteJobs[jobIndex] = Maco.favoriteJobs[newIndex];
                Maco.favoriteJobs[newIndex] = temp;
            } else if (direction === 'down' && jobIndex < Maco.favoriteJobs.length - 1) {
                const temp = Maco.favoriteJobs[jobIndex];
                Maco.favoriteJobs[jobIndex] = Maco.favoriteJobs[newIndex];
                Maco.favoriteJobs[newIndex] = temp;
            }
            Maco.favoriteJobsTablePosition.content = $(".Maco2window .tw2gui_scrollpane_clipper_contentpane").css("top");
            Maco.favoriteJobsTablePosition.scrollbar = $(".Maco2window .tw2gui_scrollbar_pulley").css("top");
            Maco.debouncedSaveAll(3000);
            Maco.selectTab("favoriteJobs");
        });
        return buttonShift;
    };
    Maco.createRemoveFavoriteJobButton = function(jobIndex) {
        var buttonRemove = document.createElement("button");
        buttonRemove.style.cssText = "width: 16px; height: 19px; background: url('https://westsk.innogamescdn.com/images/window/messages/icons.png?2') repeat scroll 0 0 transparent; background-position: -292px -4px; margin: 0px; padding: 0; border: none; outline: none; display: inline-block; cursor: pointer; user-select: none; font-size: 13px; white-space: nowrap; line-height: 29px;";
        buttonRemove.addEventListener("click", function() {
            Maco.favoriteJobs.splice(jobIndex,1);
            Maco.favoriteJobsTablePosition.content = $(".Maco2window .tw2gui_scrollpane_clipper_contentpane").css("top");
            Maco.favoriteJobsTablePosition.scrollbar = $(".Maco2window .tw2gui_scrollbar_pulley").css("top");
            Maco.debouncedSaveAll(2000);
            Maco.selectTab("favoriteJobs");
        });
        return buttonRemove;
    };
    Maco.createRemoveJobButton = function(x,y,id) {
        var buttonRemove = new west.gui.Button("Remove", function() {
            Maco.removeJob(x,y,id);
            Maco.addedJobsTablePosition.content = $(".Maco2window .tw2gui_scrollpane_clipper_contentpane").css("top");
            Maco.addedJobsTablePosition.scrollbar = $(".Maco2window .tw2gui_scrollbar_pulley").css("top");
            Maco.debouncedSaveAll(2000);
            Maco.selectTab("addedJobs");
        });
        buttonRemove.setWidth(80);
        return buttonRemove.getMainDiv();
    };
    Maco.createComboxFavoriteJobSets = function(savedJobIndex, addedJobIndex) {
        return Maco.addComboboxSetItems(new west.gui.Combobox().setWidth(60), Maco.favoriteJobs[savedJobIndex].set)
            .addListener(function(set) {
                Maco.favoriteJobs[savedJobIndex].set = set;
                if (addedJobIndex !== -1) {
                    Maco.addedJobs[addedJobIndex].setSet(set);
                }
                Maco.debouncedSaveAll(2000);
            })
            .getMainDiv();
    };
    Maco.createComboxJobSets = function(x,y,id) {
        return Maco.addComboboxSetItems(new west.gui.Combobox().setWidth(60), Maco.getJobSet(x,y,id))
            .addListener(function(set) {
                Maco.setJobSet(x,y,id, set);
                if (Maco.favoriteJobs.some(job => job.id === id)) {
                    Maco.updateFavoriteJobs(id, true, set);
                }
                Maco.debouncedSaveAll(2000);
            })
            .getMainDiv();
    };
    Maco.addWardrobeIcon = function(setName, enableOverflow = false) {
        const iconStyle = 'background: url(/images/tw2gui/iconset.png) repeat -32px 80px; transform: scale(0.8); transform-origin: center; width: 16px; height: 16px; display: inline-block; flex-shrink: 0;';
        const icon = `<span style="${iconStyle}"></span>`;

        const textStyle = enableOverflow
            ? 'white-space: nowrap;'
            : 'white-space: nowrap; overflow: hidden; text-overflow: ellipsis; display: inline-block; max-width: 100%;';

        return `<span style="display: flex; align-items: center; gap: 3px; max-width: 100%;">
                    ${icon}
                    <span style="${textStyle}">${setName}</span>
                </span>`;
    };
    Maco.addComboboxSetItems = function(combobox, toSelect = -1, defaultText = "None") {
        combobox.addItem(-1, defaultText);

        Maco.sets.forEach((set, key) => {
            combobox.addItem(key, set.name);
        });

        Maco.wardrobe.forEach((set, setId) => {
            combobox.addItem(setId, Maco.addWardrobeIcon(set.name, true));
        });

        if (Maco.sets.size <= toSelect && !Maco.wardrobe.has(toSelect)) {
            combobox.addItem(toSelect, "null");
        }

        if (!Maco.sets.has(toSelect) && !Maco.wardrobe.has(toSelect)) {
            toSelect = -1;
        }

        combobox.select(toSelect);
        return combobox;
    };
    Maco.createSetGui = function() {
        if (Maco.sets.size === 0) return $("<span style=\'font-size:20px'\>No sets available</span>");
        var htmlSkel = $("<div id=\'Maco_sets_window'\ style=\'display:block; position:relative; width:650px; height:430px;'\><div id=\'Maco_sets_left' style=\'display:block; position:absolute; width:270px; height:390px; top:0px; left:0px;'\></div><div id=\'Maco_sets_right' style=\'display:block; position:absolute; width:300px; height:410px; top:0px; left:325px'\></div></div>");
        var combobox = Maco.addComboboxSetItems(new west.gui.Combobox("combobox_sets").setWidth(140), Maco.selectedSet)
            .addListener(function(value) {
                Maco.selectedSet = value;
                Maco.selectTab("sets");
            });

        var buttonEquipSet = new west.gui.Button("Equip set", function() {
            Maco.equipSet(Maco.selectedSet);
        });

        var buttonSelectTravelSet = new west.gui.Button("Set", function() {
            Maco.travelSet = Maco.selectedSet === -1 ? -2 : Maco.selectedSet;
            Maco.debouncedSaveAll(3000);
            Maco.selectTab("sets");
        }).setWidth(45);
        var buttonSelectJobSet = new west.gui.Button("Set", function() {
            Maco.jobSet = Maco.selectedSet;
            Maco.setSetForAllJobs(Maco.jobSet);
            Maco.setSetForFavoriteJobs(Maco.jobSet);
            Maco.debouncedSaveAll(3000);
            Maco.selectTab("sets");
        }).setWidth(45);
        var buttonSelectHealthSet = new west.gui.Button("Set", function() {
            Maco.healthSet = Maco.selectedSet === -1 ? -3 : Maco.selectedSet;
            Maco.debouncedSaveAll(3000);
            Maco.selectTab("sets");
        }).setWidth(45);
        var buttonSelectRegenerationSet = new west.gui.Button("Set", function() {
            Maco.regenerationSet = Maco.selectedSet;
            Maco.debouncedSaveAll(3000);
            Maco.selectTab("sets");
        }).setWidth(45);
        var buttonSelectBuildSet = new west.gui.Button("Set", function() {
            Maco.build.set = Maco.selectedSet;
            Maco.debouncedSaveAll(3000);
            Maco.selectTab("sets");
        }).setWidth(45);
        var buttonSelectAttackSet = new west.gui.Button("Set", function() {
            Maco.settings.fortBattle.attackSet = Maco.selectedSet;
            Maco.debouncedSaveAll(3000);
            Maco.selectTab("sets");
        }).setWidth(45);
        var buttonSelectDefendSet = new west.gui.Button("Set", function() {
            Maco.settings.fortBattle.defSet = Maco.selectedSet;
            Maco.debouncedSaveAll(3000);
            Maco.selectTab("sets");
        }).setWidth(45);

        function getSetText(setKey, defaultText = "AUTO_CALC") {
            if (Maco.sets.has(setKey)) {
                return `<b style="white-space: nowrap; overflow: hidden; text-overflow: ellipsis;">${Maco.sets.get(setKey).name}</b>`;
            }
            if (Maco.wardrobe.has(setKey)) {
                return `<b style="height:15px; overflow: hidden;">${Maco.addWardrobeIcon(Maco.wardrobe.get(setKey).name)}</b>`;
            }
            return `<p>${defaultText}</p>`;
        }

        var travelSetText = getSetText(Maco.travelSet);
        var jobSetText = getSetText(Maco.jobSet, "None");
        var healthSetText = getSetText(Maco.healthSet);
        var regenerationSetText = getSetText(Maco.regenerationSet, "None");
        var buildSetText = getSetText(Maco.build.set);
        var attackSetText = getSetText(Maco.settings.fortBattle.attackSet);
        var defendSetText = getSetText(Maco.settings.fortBattle.defSet);

        const createSetRow = (label, text, button) => {
            return $("<div>").css({
                display: "flex",
                width: "100%",
                "justify-content": "space-between",
                "align-items": "center" // Ensures elements stay aligned
            }).append(
                $("<span>").css({
                    display: "inline-flex",
                    "align-items": "center",
                    gap: "8px",
                    overflow: "hidden"
                }).html("<p><i>" + label + ":</i></p> ").append(text),
                button.getMainDiv()
            );
        };

        const groupframe = new west.gui.Groupframe()
            .appendToContentPane(combobox.getMainDiv())
            .appendToContentPane($("<br>"))
            .appendToContentPane(
                $("<div>").css({
                    display: "flex",
                    "flex-direction": "column",
                    "justify-content": "space-between",
                    "height": "100%",
                    "flex-grow": "1"
                }).append(
                    createSetRow("Travel", travelSetText, buttonSelectTravelSet),
                    createSetRow("Job set", jobSetText, buttonSelectJobSet),
                    createSetRow("Health", healthSetText, buttonSelectHealthSet),
                    createSetRow("Regen", regenerationSetText, buttonSelectRegenerationSet),
                    createSetRow("Build", buildSetText, buttonSelectBuildSet),
                    createSetRow("Fort Attack", attackSetText, buttonSelectAttackSet),
                    createSetRow("Fort Defend", defendSetText, buttonSelectDefendSet)
                )
            )
            .getMainDiv();

        $(groupframe).css({'height':'370px', 'padding-top':'10px', 'padding-bottom':'10px', 'white-space':'nowrap', 'overflow':'hidden'});
        $(groupframe).find(".tw2gui_groupframe_content_pane").css({
            display: "flex",
            "flex-direction": "column",
            "height": "340px",
            "justify-content": "space-between",
            "align-items": "stretch"
        });

        var left = $("<div></div>").append(groupframe);
        var right = $("<div style=\'display:block; position:relative; width:300px; height:410px;'\></div>");

        //equip button
        $(buttonEquipSet.getMainDiv()).css({'position':'absolute', 'top':'9px', 'right':'43px'}).appendTo(right);
        //head div
        right.append("<div class=\'wear_head wear_slot'\ style=\'display:block;position:absolute;left:50px;top:1px;width:93px;height:94px;background:url(https://westzz.innogamescdn.com/images/window/wear/bg_sprite.png) 0 0 no-repeat;background-position: -95px 0;'\></div>");
        //chest div
        right.append("<div class=\'wear_body wear_slot'\ style=\'display:block;position:absolute;left:50px;top:106px;width:95px;height:138px;background:url(https://westzz.innogamescdn.com/images/window/wear/bg_sprite.png) 0 0 no-repeat;background-position:0 0;'\></div>");
        //pants div
        right.append("<div class=\'wear_pants wear_slot'\ style=\'display:block;position:absolute;left:50px;top:258px;width:93px;height:138px;background:url(https://westzz.innogamescdn.com/images/window/wear/bg_sprite.png) 0 0 no-repeat;background-position:0 0;'\></div>");
        //neck div
        right.append("<div class=\'wear_neck wear_slot'\ style=\'display:block;position:absolute;left:-27px;top:1px;width:74px;height:74px;background:url(https://westzz.innogamescdn.com/images/window/wear/bg_sprite.png) 0 0 no-repeat;background-position:-189px 0;'\></div>");
        //right arm div
        right.append("<div class=\'wear_right_arm wear_slot'\ style=\'display:block;position:absolute;left:-44px;top:79px;width:95px;height:138px;background:url(https://westzz.innogamescdn.com/images/window/wear/bg_sprite.png) 0 0 no-repeat;background-position:0 0;'\></div>");
        //animal div
        right.append("<div class=\'wear_animal wear_slot'\ style=\'display:block;position:absolute;left:-44px;top:223px;width:93px;height:94px;background:url(https://westzz.innogamescdn.com/images/window/wear/bg_sprite.png) 0 0 no-repeat;background-position:-95px 0;'\></div>");
        //yield div
        right.append("<div class=\'wear_yield wear_slot'\ style=\'display:block;position:absolute;left:-27px;top:321px;width:74px;height:74px;background:url(https://westzz.innogamescdn.com/images/window/wear/bg_sprite.png) 0 0 no-repeat;background-position:-189px 0;'\></div>");
        //left arm div
        right.append("<div class=\'wear_left_arm wear_slot'\ style=\'display:block;position:absolute;left:147px;top:52px;width:95px;height:138px;background:url(https://westzz.innogamescdn.com/images/window/wear/bg_sprite.png) 0 0 no-repeat;background-position:0 0;'\></div>");
        //belt div
        right.append("<div class=\'wear_belt wear_slot'\ style=\'display:block;position:absolute;left:147px;top:200px;width:93px;height:94px;background:url(https://westzz.innogamescdn.com/images/window/wear/bg_sprite.png) 0 0 no-repeat;background-position:-95px 0;'\></div>");
        //boots div
        right.append("<div class=\'wear_foot wear_slot'\ style=\'display:block;position:absolute;left:147px;top:302px;width:93px;height:94px;background:url(https://westzz.innogamescdn.com/images/window/wear/bg_sprite.png) 0 0 no-repeat;background-position:-95px 0;'\></div>");

        if (Maco.selectedSet !== -1) {
            const keys = ["head","body","pants","neck","right_arm","animal","yield","left_arm","belt","foot"];
            Maco.insertSetImages(right, keys);
        }

        $("#Maco_sets_left", htmlSkel).append(left);
        $("#Maco_sets_right", htmlSkel).append(right);
        return htmlSkel;
    };
    Maco.insertSetImages = function(html, keys) {
        function getImageSkel() {
            return $("<img src=\''\>");
        }

        if (Maco.sets.has(Maco.selectedSet)) {
            for (let i = 0; i < keys.length; i++) {
                if (Maco.sets.get(Maco.selectedSet)[keys[i]] != null) {
                    $(".wear_" + keys[i], html).append(getImageSkel().attr("src", Maco.getItemImage(Maco.sets.get(Maco.selectedSet)[keys[i]])));
                }
            }
        } else if (Maco.wardrobe.has(Maco.selectedSet)) {
            const wardrobeItems = Maco.wardrobe.get(Maco.selectedSet).items;

            for (let i = 0; i < keys.length; i++) {
                const item = wardrobeItems.find(itemId => ItemManager.get(itemId).type === keys[i]);
                if (item) {
                    $(".wear_" + keys[i], html).append(
                        getImageSkel().attr("src", Maco.getItemImage(item))
                    );
                }
            }
        }

        return html;
    };
    Maco.createConsumablesTab = function() {
        var htmlSkel = $("<div id=\'consumables_overview'\></div>");
        var html = $("<div class = \'consumables_filter'\ style=\'position:relative;'\><div id=\'filter_text'\style=\'position:absolute;top:10px;left:10px;'\></div><div id=\'energy_consumables'\style=\'position:absolute;top:8px;left:56px;'\></div><div id=\'motivation_consumables'\style=\'position:absolute;top:8px;left:207px;'\></div><div id=\'health_consumables'\style=\'position:absolute;top:8px;left:375px;'\></div><div id=\'buff_consumables'\style=\'position:absolute;top:8px;left:523px;'\></div></div>");

        const consumableList = Maco.filterConsumables(Maco.consumableSelection.energy, Maco.consumableSelection.motivation, Maco.consumableSelection.health, Maco.consumableSelection.buffs);
        const consumablesUsed = Maco.diagnostics.consumablesUsed || [];

        consumableList.forEach(consumable => { // Calculate usedCount for each consumable
            consumable.usedCount = consumablesUsed.filter(consumableName => consumableName.includes(consumable.name)).length;
        });

        consumableList.sort((a, b) => { // Sort consumableList by usedCount in descending order, then sort selected items first
            if (a.usedCount !== b.usedCount) {
                return b.usedCount - a.usedCount;
            } else if (a.selected !== b.selected) {
                return a.selected ? -1 : 1;
            } else if (a.hasBattleBonus !== b.hasBattleBonus) {
                return a.hasBattleBonus ? 1 : -1;
            }
            return consumableList.indexOf(a) - consumableList.indexOf(b);
        });

        var table = new west.gui.Table();
        table.addColumn("consumIcon","consumIcon").addColumn("consumName","consumName").addColumn("consumEnergy","consumEnergy").addColumn("consumMotivation","consumMotivation").addColumn("consumHealth","consumHealth").addColumn("consumBuffs","consumBuffs").addColumn("consumSelected","consumSelected");
        table.appendToCell("head","consumIcon","Count").appendToCell("head","consumName","Name").appendToCell("head","consumEnergy","Energy").appendToCell("head","consumMotivation","Motivation").appendToCell("head","consumHealth","Health").appendToCell("head","consumBuffs","Buffs").appendToCell("head","consumSelected","Use");

        for (let i = 0; i < consumableList.length; i++) {
            var totalCount = consumableList[i].count;
            var usedCount = consumableList[i].usedCount;
            var countText = totalCount + (usedCount > 0 ? " (-" + usedCount + ")" : "");
            var checkbox = new west.gui.Checkbox()
                .setSelected(consumableList[i].selected)
                .setId(consumableList[i].id)
                .setCallback(function() {
                    Maco.changeConsumableSelection(parseInt(this.divMain.attr("id")),this.isSelected());
                    Maco.consumablesTablePosition.content = $(".Maco2window .tw2gui_scrollpane_clipper_contentpane").css("top");
                    Maco.consumablesTablePosition.scrollbar = $(".Maco2window .tw2gui_scrollbar_pulley").css("top");
                    Maco.debouncedSaveAll(3000);
                });
            var buffs = '';
            if (consumableList[i].xp + consumableList[i].money + consumableList[i].product + consumableList[i].luck + consumableList[i].travel + consumableList[i].other + consumableList[i].hiding + consumableList[i].settingTraps === 0 && !consumableList[i].hasBattleBonus) {
                buffs = "No buffs";
            } else {
                buffs += "<div style='line-height: 1.3; display: flex; align-items: center;'>";

                if (consumableList[i].travel !== 0) buffs += "<img src='https://westsk.innogamescdn.com/images/buffs/travel.jpg' style='width: 25px; height: 25px; vertical-align: middle; margin-right: 5px;'>";
                else if (consumableList[i].hasBattleBonus) buffs += "<img src='https://westsk.innogamescdn.com/images/buffs/items.jpg' style='width: 25px; height: 25px; vertical-align: middle; margin-right: 5px;'>";
                else buffs += "<img src='https://westsk.innogamescdn.com/images/buffs/character.jpg' style='width: 25px; height: 25px; vertical-align: middle; margin-right: 5px;'>";

                buffs += "<div>";

                if (consumableList[i].xp !== 0) buffs += "<span>+" + consumableList[i].xp + "% XP</span><br>";
                if (consumableList[i].money !== 0) buffs += "<span>+" + consumableList[i].money + "% Money</span><br>";
                if (consumableList[i].product !== 0) buffs += "<span>+" + consumableList[i].product + "% Product</span><br>";
                if (consumableList[i].luck !== 0) buffs += "<span>+" + consumableList[i].luck + "% Luck</span><br>";
                if (consumableList[i].travel !== 0) buffs += "<span>+" + consumableList[i].travel + "% Speed</span><br>";
                if (consumableList[i].other !== 0 && (consumableList[i].xp + consumableList[i].money + consumableList[i].product + consumableList[i].luck + consumableList[i].travel === 0)) {
                    buffs += "<span>+Attributes..</span><br>";
                }
                if (consumableList[i].hasBattleBonus || consumableList[i].id === 54382000 || (consumableList[i].hiding !== 0 || consumableList[i].settingTraps !== 0) && !consumableList[i].hasCooldown) {
                    buffs += "<span>BATTLE</span><br>";
                }
                if (consumableList[i].duration !== 0) {
                    if (consumableList[i].duration === 1) buffs += "<span>" + consumableList[i].duration + " Hour</span><br>";
                    else buffs += "<span>" + consumableList[i].duration + " Hours</span><br>";
                } else if (consumableList[i].uses !== 0) {
                    if (consumableList[i].uses === 1) buffs += "<span>" + consumableList[i].uses + " Use</span><br>";
                    else buffs += "<span>" + consumableList[i].uses + " Uses</span><br>";
                }

                buffs += "</div>";
                buffs += "</div>";
            }
            table.appendRow()
                .appendToCell(-1, "consumIcon", Maco.getConsumableIcon(consumableList[i], countText))
                .appendToCell(-1, "consumName", consumableList[i].name + "&nbsp;&nbsp; ")
                .appendToCell(-1, "consumEnergy", consumableList[i].energy)
                .appendToCell(-1, "consumMotivation", consumableList[i].motivation)
                .appendToCell(-1, "consumHealth", consumableList[i].health)
                .appendToCell(-1, "consumBuffs", buffs)
                .appendToCell(-1, "consumSelected", checkbox.getMainDiv())
                .getRow().css("opacity", totalCount < 1 ? 0.5 : 1);
        }
        var buttonSelectDefault = new west.gui.Button("Default", function() {
            Maco.defaultConsumablesSelection();
            Maco.selectTab("consumables");
            Maco.debouncedSaveAll(500);
        });
        var buttonSelectDefaultDiv = buttonSelectDefault.getMainDiv();
        $(buttonSelectDefaultDiv).css({
            'margin-left': '-10px',
        });
        var buttonDeselectBuffs = new west.gui.Button("Deselect buffs", function() {
            Maco.deselectConsumablesWithBuffs();
            Maco.selectTab("consumables");
            Maco.debouncedSaveAll(500);
        });
        var buttonDeselectBuffsDiv = buttonDeselectBuffs.getMainDiv();
        $(buttonDeselectBuffsDiv).css({
            'margin-left': '-10px',
        });
        var buttonSelect = new west.gui.Button("Select all", function() {
            Maco.changeSelectionAllConsumables(true);
            Maco.selectTab("consumables");
            Maco.debouncedSaveAll(500);
        });
        var buttonSelectDiv = buttonSelect.getMainDiv();
        $(buttonSelectDiv).css({
            'margin-left': '-40px',
        });
        var buttonDeselect = new west.gui.Button("Deselect all", function() {
            Maco.changeSelectionAllConsumables(false);
            Maco.selectTab("consumables");
            Maco.debouncedSaveAll(500);
        });
        var buttonDeselectDiv = buttonDeselect.getMainDiv();
        $(buttonDeselectDiv).css({
            'margin-left': '0px',
        });
        table.appendToFooter("consumEnergy", buttonSelectDiv);
        table.appendToFooter("consumMotivation", buttonDeselectDiv);
        table.appendToFooter("consumBuffs", buttonDeselectBuffsDiv);
        htmlSkel.append(table.getMainDiv());

        var refreshTab = function() {
            $(".Maco2window .tw2gui_scrollpane_clipper_contentpane").css({"top":"0px"});
            $(".Maco2window .tw2gui_scrollbar_pulley").css({"top":"0px"});
            Maco.selectTab("consumables");
        };
        var checkboxEnergyConsumes = new west.gui.Checkbox()
            .setLabel("Energy consumables")
            .setSelected(Maco.consumableSelection.energy)
            .setCallback(function() {
                Maco.consumableSelection.energy = this.isSelected();
                refreshTab();
            });
        var checkboxMotivationConsumes = new west.gui.Checkbox()
            .setLabel("Motivation consumables")
            .setSelected(Maco.consumableSelection.motivation)
            .setCallback(function() {
                Maco.consumableSelection.motivation = this.isSelected();
                refreshTab();
            });
        var checkboxHealthConsumes = new west.gui.Checkbox()
            .setLabel("Health consumables")
            .setSelected(Maco.consumableSelection.health)
            .setCallback(function() {
                Maco.consumableSelection.health = this.isSelected();
                refreshTab();
            });
        var checkboxBuffs = new west.gui.Checkbox()
            .setLabel("Buffs")
            .setSelected(Maco.consumableSelection.buffs)
            .setCallback(function() {
                Maco.consumableSelection.buffs = this.isSelected();
                refreshTab();
            });
        $("#filter_text",html).append("<div><b>Filter: </b></div>");
        $("#energy_consumables",html).append(checkboxEnergyConsumes.getMainDiv());
        $("#motivation_consumables",html).append(checkboxMotivationConsumes.getMainDiv());
        $("#health_consumables",html).append(checkboxHealthConsumes.getMainDiv());
        $("#buff_consumables",html).append(checkboxBuffs.getMainDiv());
        htmlSkel.append(html);
        
        var lastConsumUsed = "none";
        switch (consumablesUsed.length) {
            case 0:
                break;
            case 1: 
                lastConsumUsed = consumablesUsed.at(-1);
                break;
            case 2:
                lastConsumUsed = consumablesUsed.at(-1) + ", " + consumablesUsed.at(-2);
                break;
            case 3:
                lastConsumUsed = consumablesUsed.at(-1) + ", " + consumablesUsed.at(-2) + ", " + consumablesUsed.at(-3);
                break;
            default:
                lastConsumUsed = consumablesUsed.at(-1) + ", " + consumablesUsed.at(-2) + ", " + consumablesUsed.at(-3) + "...";
                break;
        }
        var lastConsumUsedText = $("<div><b>Last used: &nbsp;</b>" + lastConsumUsed + "</div>");
        lastConsumUsedText.css('margin-top', '39px');
        lastConsumUsedText.css('margin-left', '10px');
        htmlSkel.append(lastConsumUsedText);

        return htmlSkel;
    };
    Maco.addSleepPlacesItems = function(combobox) {
        combobox.addItem(-2, "None");
        if (Maco.homeTown != null) {
            combobox.addItem(-1, Maco.homeTown.name);
        }
        for (let i = 0; i < Maco.allianceForts.length; i++) {
            var type = (Maco.allianceForts[i].type === 0) ? "Small" : (Maco.allianceForts[i].type === 1) ? "Medium" : "Big";
            combobox.addItem(i, Maco.allianceForts[i].name + "  -  " + type);
        }
    };
    Maco.addUpcomingFortBattles = function(combobox) {
        Maco.updateFortBattles();
        if (Maco.battles.size === 0) {
            combobox.addItem(-1, "None");
        }
        for (const [fortId, battle] of Maco.battles) {
            const battleTimer = formatTime(Math.max(0, Math.floor((battle.start - new Date().getTime()) / 1000)));
            combobox.addItem(fortId, battle.title + " - " + battleTimer);
        }
    };
    Maco.formatInputNumber = function(elementID) {
        // Wait for the text field to be appended to the DOM
        setTimeout(function() {
            $(elementID).on('input', 'input', function(event) {
                var currentValue = event.target.value;
                var digitsOnly = currentValue.replace(/\D/g, '');
                event.target.value = formatNumber(digitsOnly);
            });
        }, 0);
    };
    Maco.createSettingsGui = function() {
        var htmlSkel = $("<div id=\'settings_overview'\ style =\'margin-left: 10px; margin-top: 5px; overflow: hidden; white-space: nowrap;'\></div>");

        var htmlAddEnergy = $("<div></div>").css({'display': 'inline-block'});
        var checkboxAddEnergy = new west.gui.Checkbox()
            .setLabel("<span>Add energy </span>")
            .setSelected(Maco.settings.addEnergy)
            .setCallback(function() {
                Maco.settings.addEnergy = !Maco.settings.addEnergy;
                if (Maco.settings.addEnergy) {
                    $("#optional_energy_container").css('visibility','visible');
                    if (Maco.settings.addEnergyOptional) {
                        $("#optional_energy_textfields").css('visibility','visible');
                    }
                } else {
                    $("#optional_energy_container").css('visibility','hidden');
                    $("#optional_energy_textfields").css('visibility','hidden');
                }
            });
        htmlAddEnergy.append(checkboxAddEnergy.getMainDiv());
        var htmlAddEnergyOptional = $("<div id='optional_energy_container'></div>");
        htmlAddEnergyOptional.css({
            'display': 'inline-flex',
            'align-items': 'center',
            'position': 'relative',
            'left': '62px',
            'visibility': (Maco.settings.addEnergy) ? 'visible' : 'hidden'
        });
        var htmlAddEnergyOptionalWrapper = $("<div id='optional_energy_wrapper'></div>").css({
            'display': 'flex',
            'align-items': 'center',
            'height': '26px',
        });
        htmlAddEnergyOptionalWrapper.attr('title', Maco.explainerTranslations[Maco.translationLang].explainer_1);
        var checkboxAddEnergyOptional = new west.gui.Checkbox()
            .setLabel("<span> Continuously refill </span>")
            .setSelected(Maco.settings.addEnergyOptional)
            .setCallback(function() {
                Maco.settings.addEnergyOptional = !Maco.settings.addEnergyOptional;
                if (Maco.settings.addEnergyOptional) {
                    $("#optional_energy_textfields").css('visibility','visible');
                } else {
                    $("#optional_energy_textfields").css('visibility','hidden');
                }
            });
        htmlAddEnergyOptionalWrapper.append(checkboxAddEnergyOptional.getMainDiv());
        var htmlAddEnergyOptionalTextFields = $("<div id='optional_energy_textfields'></div>").css({
            'display': 'inline-block',
            'margin-left': '4px',
            'visibility': (Maco.settings.addEnergy && Maco.settings.addEnergyOptional) ? 'visible' : 'hidden'
        });
        var addEnergyOptionalMinTextField = new west.gui.Textfield("addEnergyOptionalMin")
            .setWidth(35)
            .setValue(Maco.settings.addEnergyOptionalMin)
            .onlyNumeric();
        var addEnergyOptionalMaxTextField = new west.gui.Textfield("addEnergyOptionalMax")
            .setWidth(35)
            .setValue(Maco.settings.addEnergyOptionalMax)
            .onlyNumeric();
        var checkboxAllowMotivation = new west.gui.Checkbox()
            .setLabel("<span> Allow motivation </span>")
            .setSelected(Maco.settings.allowMotivationOptional)
            .setCallback(function() {
                Maco.settings.allowMotivationOptional = this.isSelected();
            });
        checkboxAllowMotivation.getMainDiv().attr('title', Maco.explainerTranslations[Maco.translationLang].explainer_30);

        htmlAddEnergyOptionalTextFields.append("<span> % </span>");
        htmlAddEnergyOptionalTextFields.append(addEnergyOptionalMinTextField.getMainDiv());
        htmlAddEnergyOptionalTextFields.append("<span> - </span>");
        htmlAddEnergyOptionalTextFields.append(addEnergyOptionalMaxTextField.getMainDiv());
        htmlAddEnergyOptionalTextFields.append("<span style='margin-right:10px;'></span>");
        htmlAddEnergyOptionalWrapper.append(htmlAddEnergyOptionalTextFields);
        htmlAddEnergyOptional.append(htmlAddEnergyOptionalWrapper);
        htmlAddEnergyOptional.append(checkboxAllowMotivation.getMainDiv());

        var htmlAddMotivation = $("<div style='width: fit-content;'></div>");
        htmlAddMotivation.attr('title', Maco.explainerTranslations[Maco.translationLang].explainer_12);
        var checkboxAddMotivation = new west.gui.Checkbox()
            .setLabel("Add motivation ")
            .setSelected(Maco.settings.addMotivation)
            .setCallback(function() {
                Maco.settings.addMotivation = !Maco.settings.addMotivation;
            });
        htmlAddMotivation.append(checkboxAddMotivation.getMainDiv());

        var htmlAddHealth = $("<div></div>").css({'display': 'inline-block', 'margin-bottom': '3px'});
        htmlAddHealth.attr('title', Maco.explainerTranslations[Maco.translationLang].explainer_2);
        var checkboxAddHealth = new west.gui.Checkbox()
            .setLabel("Add health ")
            .setSelected(Maco.settings.addHealth)
            .setCallback(function() {
                Maco.settings.addHealth = !Maco.settings.addHealth;
            });
        htmlAddHealth.append(checkboxAddHealth.getMainDiv());

        var htmlhealthStop = $("<div style='margin-left: 65.5px; display: inline-flex; align-items: center; text-align: center; height: 26px; line-height: 26px;'></div>");
        htmlhealthStop.attr('title', Maco.explainerTranslations[Maco.translationLang].explainer_2);
        htmlhealthStop.append("<span style='margin-right: 5px;'>[Stop]</span>");
        var htmlhealthStopValue = $("<div style='display: inline-block;'></div>");
        htmlhealthStopValue.append("<span> Minimum HP </span>");
        var healthStopValueTextfiled = new west.gui.Textfield("healthStopValue")
            .setWidth(50)
            .setValue(Maco.settings.healthStopValue)
            .onlyNumeric();
        htmlhealthStopValue.append(healthStopValueTextfiled.getMainDiv());
        var htmlhealthStopPercent = $("<div></div>");
        htmlhealthStopPercent.css({
            'display': 'inline-block',
            'margin-left': '15px'
        });
        htmlhealthStopPercent.append("<span>Minimum HP % </span>");
        var healthStopPercentTextfiled = new west.gui.Textfield("healthStopPercent")
            .setWidth(35)
            .setValue(Maco.settings.healthStopPercent)
            .onlyNumeric();
        htmlhealthStopPercent.append(healthStopPercentTextfiled.getMainDiv());
        htmlhealthStop.append(htmlhealthStopValue);
        htmlhealthStop.append(htmlhealthStopPercent);

        var htmlAddBuffs = $("<div></div>").css({'display': 'inline-block', 'margin-bottom': '3px'});
        htmlAddBuffs.attr('title', Maco.explainerTranslations[Maco.translationLang].explainer_4);
        var htmlBuffsDiv = $("<div id='buff_checkboxes'></div>").css({
            'display': 'inline-flex', 'justify-content': 'space-between', 'width': '350px', 'margin-left': '73px',
            'visibility': (Maco.settings.addBuffs) ? 'visible' : 'hidden'
        });
        var checkboxAddBuffs = new west.gui.Checkbox()
            .setLabel("Add buffs ")
            .setSelected(Maco.settings.addBuffs)
            .setCallback(function() {
                Maco.settings.addBuffs = !Maco.settings.addBuffs;
                if (Maco.settings.addBuffs) {
                    $("#buff_checkboxes").css('visibility','visible');
                } else {
                    $("#buff_checkboxes").css('visibility','hidden');
                }
            });
        htmlAddBuffs.append(checkboxAddBuffs.getMainDiv());
        var checkboxAddXpBuff = new west.gui.Checkbox()
            .setLabel("XP ")
            .setSelected(Maco.settings.addXpBuff)
            .setCallback(function() {
                Maco.settings.addXpBuff = !Maco.settings.addXpBuff;
            });
        var checkboxAddProductBuff = new west.gui.Checkbox()
            .setLabel("Product ")
            .setSelected(Maco.settings.addProductBuff)
            .setCallback(function() {
                Maco.settings.addProductBuff = !Maco.settings.addProductBuff;
            });
        var checkboxAddMoneyBuff = new west.gui.Checkbox()
            .setLabel("Money ")
            .setSelected(Maco.settings.addMoneyBuff)
            .setCallback(function() {
                Maco.settings.addMoneyBuff = !Maco.settings.addMoneyBuff;
            });
        var checkboxAddLuckBuff = new west.gui.Checkbox()
            .setLabel("Luck ")
            .setSelected(Maco.settings.addLuckBuff)
            .setCallback(function() {
                Maco.settings.addLuckBuff = !Maco.settings.addLuckBuff;
            });
        var checkboxAddTravelBuff = new west.gui.Checkbox()
            .setLabel("Travel ")
            .setSelected(Maco.settings.addTravelBuff)
            .setCallback(function() {
                Maco.settings.addTravelBuff = !Maco.settings.addTravelBuff;
            });
        htmlBuffsDiv.append(checkboxAddXpBuff.getMainDiv());
        htmlBuffsDiv.append(checkboxAddLuckBuff.getMainDiv());
        htmlBuffsDiv.append(checkboxAddMoneyBuff.getMainDiv());
        htmlBuffsDiv.append(checkboxAddProductBuff.getMainDiv());
        htmlBuffsDiv.append(checkboxAddTravelBuff.getMainDiv());
        htmlAddBuffs.append(htmlBuffsDiv);
        const checkboxes = {
            'addXpBuff': checkboxAddXpBuff,
            'addProductBuff': checkboxAddProductBuff,
            'addMoneyBuff': checkboxAddMoneyBuff,
            'addLuckBuff': checkboxAddLuckBuff,
        };
        let callbackEnabled = true;
        for (const key in checkboxes) {
            checkboxes[key].setCallback(function() {
                if (!callbackEnabled) return;
                callbackEnabled = false;
                // Update checkbox states
                const currentCheckbox = checkboxes[key];
                const currentState = Maco.settings[key];
                if (!currentState) { // Only toggle the current checkbox if it's not already checked
                    currentCheckbox.setSelected(true);
                    Maco.settings[key] = true;
                } else { // Uncheck the current checkbox
                    currentCheckbox.setSelected(false);
                    Maco.settings[key] = false;
                }
                // Reset other checkboxes
                for (const otherKey in checkboxes) {
                    if (key !== otherKey) {
                        checkboxes[otherKey].setSelected(false);
                        Maco.settings[otherKey] = false;
                    }
                }
                setTimeout(() => {
                    callbackEnabled = true;
                }, 100);
            });
        }

        var htmlBattleOptions = $("<div id='battle_options_container'></div>");
        htmlBattleOptions.css({
            'display': 'inline-block',
            'position': 'relative',
            'left': '25px',
            'visibility': (Maco.settings.fortBattle.attend) ? 'visible' : 'hidden'
        });
        var htmlRefillBattleHealthWrapper = $("<div id='battle_health_wrapper'></div>").css({
            'display': 'flex',
            'align-items': 'center',
            'height': '28px',
        });
        var htmlRefillBattleHealth = $("<div></div>");
        htmlRefillBattleHealth.attr('title', Maco.explainerTranslations[Maco.translationLang].explainer_9);
        var checkboxRefillBattleHealth = new west.gui.Checkbox()
            .setLabel("<span> Refill HP before battle </span>")
            .setSelected(Maco.settings.fortBattle.refillHealth)
            .setCallback(function() {
                Maco.settings.fortBattle.refillHealth = !Maco.settings.fortBattle.refillHealth;
                if (Maco.settings.fortBattle.refillHealth) {
                    $("#battle_health_textfield").css('visibility','visible');
                    $("#battle_health_tank").css('visibility','visible');
                } else {
                    $("#battle_health_textfield").css('visibility','hidden');
                    $("#battle_health_tank").css('visibility','hidden');
                }
            });
        var htmlBattleHealthTextField = $("<div id='battle_health_textfield'></div>").css({
            'display': 'inline-block',
            'margin-left': '4px',
            'visibility': (Maco.settings.fortBattle.attend && Maco.settings.fortBattle.refillHealth) ? 'visible' : 'hidden'
        });
        var minBattleHealthTextField = new west.gui.Textfield("minBattleHealth")
            .setWidth(35)
            .setValue(Maco.settings.fortBattle.minHealth)
            .onlyNumeric();

        var htmlRefillTank = $("<div id='battle_health_tank'></div>").css({
            'display': 'inline-flex',
            'margin-left': '10px',
            'gap': '10px',
            'visibility': (Maco.settings.fortBattle.attend && Maco.settings.fortBattle.refillHealth) ? 'visible' : 'hidden'
        });
        var htmlCheckboxRefillTank = $("<div></div>");
        htmlCheckboxRefillTank.attr('title', Maco.explainerTranslations[Maco.translationLang].explainer_18);
        var checkboxRefillTank = new west.gui.Checkbox()
            .setLabel("<span> Tank HP </span>")
            .setSelected(Maco.settings.fortBattle.isTank)
            .setCallback(function() {
                Maco.settings.fortBattle.isTank = !Maco.settings.fortBattle.isTank;
            });
        htmlCheckboxRefillTank.append(checkboxRefillTank.getMainDiv());
        htmlRefillTank.append(htmlCheckboxRefillTank);

        var htmlCheckboxOverwriteBuffTank = $("<div></div>");
        htmlCheckboxOverwriteBuffTank.attr('title', Maco.explainerTranslations[Maco.translationLang].explainer_31);
        var checkboxOverwriteBuffTank = new west.gui.Checkbox()
            .setLabel("<span> Overwrite Buff </span>")
            .setSelected(Maco.settings.fortBattle.overwriteCharacterBonus)
            .setCallback(function() {
                Maco.settings.fortBattle.overwriteCharacterBonus = !Maco.settings.fortBattle.overwriteCharacterBonus;
            });
        htmlCheckboxOverwriteBuffTank.append(checkboxOverwriteBuffTank.getMainDiv());
        htmlRefillTank.append(htmlCheckboxOverwriteBuffTank);

        var htmlCheckboxOpenFortWindow = $("<div></div>");
        htmlCheckboxOpenFortWindow.attr('title', Maco.explainerTranslations[Maco.translationLang].explainer_10);
        var checkboxOpenFortWindow = new west.gui.Checkbox()
            .setLabel("<span> Open fort window to appear online </span>")
            .setSelected(Maco.settings.fortBattle.openFortWindow)
            .setCallback(function() {
                Maco.settings.fortBattle.openFortWindow = !Maco.settings.fortBattle.openFortWindow;
            });
        htmlCheckboxOpenFortWindow.append(checkboxOpenFortWindow.getMainDiv());

        var htmlBattleConsumable = $("<div></div>").css({
            'display': 'flex',
            'align-items': 'center',
            'height': '28px'
        });
        var checkboxBattleConsumable = new west.gui.Checkbox()
            .setLabel("<span> Use consumable </span>")
            .setSelected(Maco.settings.fortBattle.useConsumable)
            .setCallback(function() {
                Maco.settings.fortBattle.useConsumable = this.isSelected();
                if (this.isSelected()) {
                    $("#battle_consumable_textfield").css('visibility','visible');
                } else {
                    $("#battle_consumable_textfield").css('visibility','hidden');
                }
            });
        var htmlBattleConsumableTextField = $("<div id='battle_consumable_textfield'></div>").css({
            'display': 'inline-block',
            'margin-left': '4px',
            'visibility': (checkboxBattleConsumable.isSelected() && Maco.settings.fortBattle.attend) ? 'visible' : 'hidden'
        });
        var battleConsumableTextField = new west.gui.Textfield("battleConsumable")
            .setWidth(100)
            .setValue(Maco.settings.fortBattle.consumable)
        htmlBattleConsumableTextField.append(battleConsumableTextField.getMainDiv());
        htmlBattleConsumable.append(checkboxBattleConsumable.getMainDiv());
        htmlBattleConsumable.append(htmlBattleConsumableTextField);

        htmlBattleHealthTextField.append("<span> - Minimum battle HP % </span>");
        htmlBattleHealthTextField.append(minBattleHealthTextField.getMainDiv());
        htmlRefillBattleHealth.append(checkboxRefillBattleHealth.getMainDiv());
        htmlRefillBattleHealth.append(htmlBattleHealthTextField);
        htmlRefillBattleHealthWrapper.append(htmlRefillBattleHealth);
        htmlRefillBattleHealthWrapper.append(htmlRefillTank);
        htmlBattleOptions.append(htmlRefillBattleHealthWrapper);
        htmlBattleOptions.append(htmlCheckboxOpenFortWindow);
        if (Maco.settings.fortBattle.consumable) {
            htmlBattleOptions.append(htmlBattleConsumable);
        }

        var htmlWorker = $("<div style='margin-bottom: 3px; width: fit-content;'></div>");
        htmlWorker.attr('title', Maco.explainerTranslations[Maco.translationLang].explainer_3);
        var checkboxWorker = new west.gui.Checkbox()
            .setLabel("Night shift worker ")
            .setSelected(Maco.settings.nightShiftWorker)
            .setCallback(function() {
                Maco.settings.nightShiftWorker = !Maco.settings.nightShiftWorker;
            });
        var htmlOpenWorker = $('<span>Open worker</span>')
            .css({
                'margin-left': '8px',
                'font-size': '11px',
                'color': '#333',                   // lighter black
                'cursor': 'pointer',
                'display': 'inline-flex',          // to align icon and text
                'align-items': 'center',
                'gap': '4px'                       // spacing between text and icon
            })
            .hover(
                function () { $(this).css('color', '#000'); },
                function () { $(this).css('color', '#333'); }
            )
            .on('click', function () {
                Maco.selectTab("favoriteJobs");
            });
        var arrowIcon = $('<span>&#x21AA;</span>').css({'font-size': '11px','color': 'inherit'});
        htmlOpenWorker.prepend(arrowIcon);
        htmlWorker.append(checkboxWorker.getMainDiv());
        htmlWorker.append(htmlOpenWorker);

        var htmlBuild = $("<div style='margin-bottom: 3px;'></div>");
        htmlBuild.attr('title', Maco.explainerTranslations[Maco.translationLang].explainer_26);
        var checkboxChurch = new west.gui.Checkbox()
            .setLabel("Build Church during night ")
            .setSelected(Maco.settings.nightBuild)
            .setCallback(function() {
                Maco.settings.nightBuild = !Maco.settings.nightBuild;
            });
        htmlBuild.append(checkboxChurch.getMainDiv());

        let autoReloadOld = Maco.settings.autoReload;
        let debounceReloadObserverId;
        function debouncedStartReloadObserver() {
            if (debounceReloadObserverId) {
                clearTimeout(debounceReloadObserverId);
            }
            debounceReloadObserverId = setTimeout(() => {
                if (Maco.settings.autoReload && !autoReloadOld && Maco.isRunning) {
                    Maco.startReloadObserver();
                    autoReloadOld = true;
                }
            }, 5000);
        }
        var htmlAutoReload = $("<div style='margin-bottom: 3px; width: fit-content;'></div>");
        htmlAutoReload.attr('title', Maco.explainerTranslations[Maco.translationLang].explainer_5);
        var checkboxAutoReload = new west.gui.Checkbox()
            .setLabel("Enable auto-refresh ")
            .setSelected(Maco.settings.autoReload)
            .setCallback(function() {
                Maco.settings.autoReload = !Maco.settings.autoReload;
                if (Maco.settings.autoReload && !autoReloadOld && Maco.isRunning) {
                    debouncedStartReloadObserver();
                }
            });
        htmlAutoReload.append(checkboxAutoReload.getMainDiv());

        var htmlEfficientTravel = $("<div style='margin-top: 3px; width: fit-content;'></div>");
        htmlEfficientTravel.attr('title', Maco.explainerTranslations[Maco.translationLang].explainer_6);
        var checkboxEfficientTravel = new west.gui.Checkbox()
            .setLabel("Efficient Travel ")
            .setSelected(Maco.settings.advancedWalkingToJob)
            .setCallback(function() {
                Maco.settings.advancedWalkingToJob = !Maco.settings.advancedWalkingToJob;
            });
        htmlEfficientTravel.append(checkboxEfficientTravel.getMainDiv());

        var htmlRegeneration = $("<div style='margin-bottom: 3px; width: fit-content;'></div>");
        var htmlCheckboxEnableRegeneration = $("<div style='display: inline-block'></div>");
        htmlCheckboxEnableRegeneration.attr('title', Maco.explainerTranslations[Maco.translationLang].explainer_11);
        var checkboxEnableRegeneration = new west.gui.Checkbox()
            .setLabel("Enable regeneration")
            .setSelected(Maco.settings.enableRegeneration)
            .setCallback(function() {
                Maco.settings.enableRegeneration = !Maco.settings.enableRegeneration;
            });

        htmlCheckboxEnableRegeneration.append(checkboxEnableRegeneration.getMainDiv());
        htmlRegeneration.append(htmlCheckboxEnableRegeneration);

        var htmlEnableAutoDeposit = $("<div style='display: flex; align-items: center; height: 26px; width: fit-content;'></div>");
        htmlEnableAutoDeposit.attr('title', Maco.explainerTranslations[Maco.translationLang].explainer_19);
        var checkboxEnableAutoDeposit = new west.gui.Checkbox()
            .setLabel("Deposit money")
            .setSelected(Maco.settings.autoMoneyDeposit.enabled)
            .setCallback(function() {
                Maco.settings.autoMoneyDeposit.enabled = !Maco.settings.autoMoneyDeposit.enabled;
                if (Maco.settings.autoMoneyDeposit.enabled) {
                    $("#deposit_money_field").css('visibility','visible');
                    $("#deposit_options_container").css('visibility','visible');
                    if (Character.homeTown.town_id === 0) {
                        $("#button_set_town").css('visibility','visible');
                    }
                } else {
                    $("#deposit_options_container").css('visibility','hidden');
                    $("#deposit_money_field").css('visibility','hidden');
                    if (!Maco.settings.fortBattle.attend) { // && !Maco.settings.enableRegeneration
                        $("#button_set_town").css('visibility','hidden');
                    }
                }
            });
        var htmlDepositAmount = $("<div id='deposit_money_field'></div>").css({
            'display': 'inline-block',
            'margin-left': '15.5px',
            'visibility': (Maco.settings.autoMoneyDeposit.enabled) ? 'visible' : 'hidden'
        });
        htmlDepositAmount.append($("<span> Deposit amount above $ </span>"));
        var htmlDepositAmountTextfiled = new west.gui.Textfield("depositAmount")
            .setWidth(90)
            .setValue(formatNumber(Maco.settings.autoMoneyDeposit.amount))
            .onlyNumeric();
        htmlDepositAmount.append(htmlDepositAmountTextfiled.getMainDiv());
        htmlEnableAutoDeposit.append(checkboxEnableAutoDeposit.getMainDiv());
        htmlEnableAutoDeposit.append(htmlDepositAmount);
        Maco.formatInputNumber("#deposit_money_field");

        var htmlDepositOptions = $("<div id='deposit_options_container'></div>");
        htmlDepositOptions.css({
            'display': 'flex',
            'align-items': 'flex-start', // center
            'flex-direction': 'column',
            'position': 'relative',
            'left': '25px',
            'visibility': (Maco.settings.autoMoneyDeposit.enabled) ? 'visible' : 'hidden'
        });
        htmlDepositOptions.attr('title', Maco.explainerTranslations[Maco.translationLang].explainer_7);
        var checkboxDepositDuelProtected = new west.gui.Checkbox()
            .setLabel("<span> Don't deposit while duel protected </span>")
            .setSelected(Maco.settings.autoMoneyDeposit.duelProtected)
            .setCallback(function() {
                Maco.settings.autoMoneyDeposit.duelProtected = this.isSelected();
            });
        var htmlAuctionDeposit = $("<div></div>").css({});
        var htmlSellerNameTextfiled = new west.gui.Textfield("auctionBidName")
            .setWidth(100)
            .setValue(Maco.settings.autoMoneyDeposit.sellerName);
        var htmlAuctionItemIdTextfiled = new west.gui.Textfield("auctionItemId")
            .setWidth(100)
            .setValue((Maco.settings.autoMoneyDeposit.auctionItemId) ? `[item=${Maco.settings.autoMoneyDeposit.auctionItemId}]` : "");
        htmlAuctionDeposit.attr('title', Maco.explainerTranslations[Maco.translationLang].explainer_32);
        htmlAuctionDeposit.append($("<span> Item ID: </span>"));
        htmlAuctionDeposit.append(htmlAuctionItemIdTextfiled.getMainDiv());
        htmlAuctionDeposit.append($("<span> Seller Name: </span>").css('margin-left','10px'));
        htmlAuctionDeposit.append(htmlSellerNameTextfiled.getMainDiv());
        htmlDepositOptions.append(htmlAuctionDeposit);
        htmlDepositOptions.append(checkboxDepositDuelProtected.getMainDiv());

        var htmlAttendBattles = $("<div style='margin-top: 13px; width: fit-content;'></div>");
        htmlAttendBattles.attr('title', Maco.explainerTranslations[Maco.translationLang].explainer_8);
        var checkboxAttendBattles = new west.gui.Checkbox()
            .setLabel("Attend battles")
            .setSelected(Maco.settings.fortBattle.attend)
            .setCallback(function() {
                Maco.settings.fortBattle.attend = !Maco.settings.fortBattle.attend;
                if (Maco.settings.fortBattle.attend) {
                    $("#battle_options_container").css('visibility','visible');
                    $("#battle_choices_container").css('visibility','visible');
                    if (Maco.settings.fortBattle.refillHealth) {
                        $("#battle_health_textfield").css('visibility','visible');
                        $("#battle_health_tank").css('visibility','visible');
                    }
                    if (Character.homeTown.town_id === 0) {
                        $("#button_set_town").css('visibility','visible');
                        if (Maco.homeTown == null) {
                            new UserMessage("Set town to deposit money before battle.", UserMessage.TYPE_HINT).show();
                        }
                    }
                    Maco.selectTab("settings");
                } else {
                    Maco.maxAllowedEnergy = 100;
                    $("#battle_choices_container").css('visibility','hidden');
                    $("#battle_options_container").css('visibility','hidden');
                    $("#battle_health_textfield").css('visibility','hidden');
                    $("#battle_health_tank").css('visibility','hidden');
                    $("#battle_consumable_textfield").css('visibility','hidden');
                    if (!Maco.settings.autoMoneyDeposit.enabled) { // && !Maco.settings.enableRegeneration
                        $("#button_set_town").css('visibility','hidden');
                    }
                }
            });
        var upcomingBattlesCombobox = new west.gui.Combobox("upcoming_battles");
        Maco.addUpcomingFortBattles(upcomingBattlesCombobox);
        upcomingBattlesCombobox = upcomingBattlesCombobox.select(Maco.settings.fortBattle.selected);
        upcomingBattlesCombobox.setWidth(120);
        upcomingBattlesCombobox.addListener(function(value) {
            Maco.settings.fortBattle.selected = value;
        });
        var htmlBattleChoices = $("<div id='battle_choices_container'></div>");
        htmlBattleChoices.css({
            'display': 'inline-block',
            'visibility': (Maco.settings.fortBattle.attend) ? 'visible' : 'hidden'
        });
        htmlBattleChoices.append($("<span>: &nbsp;</span>")); // Text infront battle choices combobox

        var battleAttackSetCombobox = Maco.addComboboxSetItems(new west.gui.Combobox().setWidth(75), Maco.settings.fortBattle.attackSet, 'AUTO_CALC')
            .addListener(function(value) {
                Maco.settings.fortBattle.attackSet = value;
            });
        var battleDefSetCombobox = Maco.addComboboxSetItems(new west.gui.Combobox().setWidth(75), Maco.settings.fortBattle.defSet, 'AUTO_CALC')
            .addListener(function(value) {
                Maco.settings.fortBattle.defSet = value;
            });

        htmlBattleChoices.append(upcomingBattlesCombobox.getMainDiv());
        htmlBattleChoices.append($("<span style='margin-left: 10px;'> Attack: </span>"));
        htmlBattleChoices.append(battleAttackSetCombobox.getMainDiv());
        htmlBattleChoices.append($("<span style='margin-left: 5px;'> Def.: </span>"));
        htmlBattleChoices.append(battleDefSetCombobox.getMainDiv());
        htmlAttendBattles.append(checkboxAttendBattles.getMainDiv());
        htmlAttendBattles.append(htmlBattleChoices);

        var buttonSetTown = new west.gui.Button(Maco.homeTown == null ? "Set Town" : "Change Town", function() {
            if (Maco.setNewHomeTown()) {
                new UserMessage("Town changed.", UserMessage.TYPE_SUCCESS).show();
                Maco.refreshTab("settings");
            } else {
                new UserMessage("Not in town.", UserMessage.TYPE_ERROR).show();
            }
        });
        var buttonSetTownDiv = $("<div></div>")
            .attr('title', Maco.explainerTranslations[Maco.translationLang].explainer_27)
            .prop('id', 'button_set_town')
            .css({
                position: 'absolute',
                bottom: '157px',
                right: '65px',
                visibility: (Character.homeTown.town_id === 0 && (Maco.settings.autoMoneyDeposit.enabled || Maco.settings.fortBattle.attend)) ? 'visible' : 'hidden'
            });
        const townNameLabel = $("<div></div>")
            .text(Maco.homeTown?.name || '')
            .css({
                'margin-top': '5px',
                'text-align': 'center',
                'font-size': '11px',
                'color': 'black'
            });
        buttonSetTownDiv.append(buttonSetTown.getMainDiv());
        buttonSetTownDiv.append(townNameLabel);

        var buttonApply = new west.gui.Button("Apply", function() {
            let error = false;
            if (isNumber(addEnergyOptionalMinTextField.getValue())) {
                var addEnergyOptionalMin = parseInt(addEnergyOptionalMinTextField.getValue());
                Maco.settings.addEnergyOptionalMin = clamp(addEnergyOptionalMin, 10, 100);
            } else {
                new UserMessage("Wrong format of energy min % value. Please set a number.", UserMessage.TYPE_ERROR).show();
                error = true;
            }
            if (isNumber(addEnergyOptionalMaxTextField.getValue())) {
                var addEnergyOptionalMax = parseInt(addEnergyOptionalMaxTextField.getValue());
                Maco.settings.addEnergyOptionalMax = clamp(addEnergyOptionalMax, Maco.settings.addEnergyOptionalMin, 100);
            } else {
                new UserMessage("Wrong format of energy max % value. Please set a number.", UserMessage.TYPE_ERROR).show();
                error = true;
            }
            if (isNumber(minBattleHealthTextField.getValue())) {
                var minBattleHealth = parseInt(minBattleHealthTextField.getValue());
                Maco.settings.fortBattle.minHealth = clamp(minBattleHealth, 40, 100);
            } else {
                new UserMessage("Wrong format of health % value. Please set a number.", UserMessage.TYPE_ERROR).show();
                error = true;
            }
            if (/^\d+(,\d+)?$/.test(battleConsumableTextField.getValue().trim())) {
                Maco.settings.fortBattle.consumable = battleConsumableTextField.getValue().trim().split(",").map(Number);
            } else {
                Maco.settings.fortBattle.consumable = null;
            }
            if (isNumber(healthStopPercentTextfiled.getValue())) {
                var healthStopPercent = parseInt(healthStopPercentTextfiled.getValue());
                Maco.settings.healthStopPercent = clamp(healthStopPercent, 10, 30);
            }
            if (isNumber(healthStopValueTextfiled.getValue())) {
                var healthStopValue = parseInt(healthStopValueTextfiled.getValue());
                Maco.settings.healthStopValue = Math.max(20, healthStopValue);
            }
            if (isNumber(htmlDepositAmountTextfiled.getValue())) {
                var depositAmount = parseInt(htmlDepositAmountTextfiled.getValue().replace(/\./g, ''));
                Maco.settings.autoMoneyDeposit.amount = Math.max(10000, depositAmount);
            }
            const itemIdVal = extractNumberFromString(htmlAuctionItemIdTextfiled.getValue());
            const sellerNameVal = htmlSellerNameTextfiled.getValue().trim();
            Maco.settings.autoMoneyDeposit.sellerName = sellerNameVal || "";
            if (isNumber(itemIdVal)) {
                Maco.settings.autoMoneyDeposit.auctionItemId = itemIdVal;
            } else {
                Maco.settings.autoMoneyDeposit.auctionItemId = "";
            }
            Maco.selectTab("settings");
            Maco.debouncedSaveAll(100);
            if (!error) new UserMessage("Saved succesfully.", UserMessage.TYPE_SUCCESS).show();
        });

        var buttonApplyDiv = buttonApply.getMainDiv();
        $(buttonApplyDiv).css({
            'position': 'absolute',
            'bottom': '20px',
            'right': '50px'
        });

        var htmlExportImport = $("<div></div>");
        htmlExportImport.css({
            'position': 'absolute',
            'bottom': '0px',
            'right': '170px',
            'transform': 'scale(0.9)'
        });
        htmlExportImport.attr('title', Maco.explainerTranslations[Maco.translationLang].explainer_16);
        var buttonExportData = new west.gui.Button("Export", function() {
            Maco.exportSettings();
        });
        var buttonImportData = new west.gui.Button("Import", function() {
            Maco.importSettings()
                .then(() => {
                    Maco.loadSavedData();
                    Maco.loadSets(function() {});
                    Maco.loadAllConsumablesSelection();
                    Maco.refreshTab("settings");
                    new UserMessage("Data successfully imported.", UserMessage.TYPE_SUCCESS).show();
                })
                .catch(error => {
                    new UserMessage("Failed to import data: " + error.message, UserMessage.TYPE_ERROR).show();
                });
        });
        buttonExportData.setWidth(70);
        buttonImportData.setWidth(70);
        htmlExportImport.append(buttonImportData.getMainDiv());
        htmlExportImport.append(buttonExportData.getMainDiv());

        htmlSkel.append(htmlAddEnergy);
        htmlSkel.append(htmlAddEnergyOptional);
        htmlSkel.append(htmlAddMotivation);
        htmlSkel.append(htmlAddHealth);
        htmlSkel.append(htmlhealthStop);
        htmlSkel.append("<br>");
        htmlSkel.append(htmlRegeneration);
        //htmlSkel.append(htmlBuild);
        htmlSkel.append(htmlAddBuffs);
        htmlSkel.append(htmlAutoReload);
        htmlSkel.append(htmlWorker);
        htmlSkel.append(htmlEfficientTravel);
        htmlSkel.append(htmlEnableAutoDeposit);
        htmlSkel.append(htmlDepositOptions);
        htmlSkel.append(buttonSetTownDiv); // Set town button
        htmlSkel.append(htmlAttendBattles);
        htmlSkel.append(htmlBattleOptions);
        htmlSkel.append("<br>");
        htmlSkel.append(buttonApplyDiv);
        htmlSkel.append(htmlExportImport);
        return htmlSkel;
    };
    Maco.createNotificationsGui = function() {
        var htmlSkel = $("<div id=\'notifications_overview'\ style = \'margin: 30px; margin-top: 10px;'\></div>");
        const saveAllConfirmation = () => Maco.debouncedSaveAll(100, () => new UserMessage("Saved successfully.", UserMessage.TYPE_SUCCESS).show());

        if (!("Notification" in globalWindow)) {
            new UserMessage("Notifications not supported in this browser", UserMessage.TYPE_ERROR).show();
        }
        // Request permission to display notifications (if not already granted)
        if (Notification.permission !== "granted") {
            Notification.requestPermission().then(function (permission) {
                if (permission !== "granted") {
                    new UserMessage("Notification permission denied", UserMessage.TYPE_ERROR).show();
                }
            });
        }

        var buttonTest = new west.gui.Button("Test", function() {
            Maco.showNotification("The West - Notification test", "Notification test message - " + timestamp(), "enabled");
        });
        buttonTest.setWidth(70);
        var buttonTestDiv = buttonTest.getMainDiv();
        buttonTestDiv.id = 'button_test_notification';
        $(buttonTestDiv).css({
            'position': 'absolute',
            'top': '50px',
            'right': '290px',
            'visibility': (Maco.settings.notifications.enabled) ? 'visible' : 'hidden'
        });

        var htmlEnable = $("<div style='display: flex; align-items: center; height: 26px; margin-bottom:3px;'></div>");
        //htmlEnable.attr('title', Maco.explainerTranslations[Maco.translationLang].explainer_255);
        var checkboxEnable = new west.gui.Checkbox()
            .setLabel("Enable notifications")
            .setSelected(Maco.settings.notifications.enabled)
            .setCallback(function() {
                Maco.settings.notifications.enabled = !Maco.settings.notifications.enabled;
                if (Maco.settings.notifications.enabled) {
                    $("#options_container").css('visibility','visible');
                    $("#button_test_notification").css('visibility','visible');
                } else {
                    $("#options_container").css('visibility','hidden');
                    $("#button_test_notification").css('visibility','hidden');
                }
                saveAllConfirmation();
            });
        htmlEnable.append(checkboxEnable.getMainDiv());

        var htmlOptions = $("<div id='options_container'></div>").css({
            'display': 'inline-block',
            'position': 'relative',
            'left': '25px',
            'visibility': (Maco.settings.notifications.enabled) ? 'visible' : 'hidden'
        });

        var htmlSilent = $("<div style='display: flex; align-items: center; height: 28px;'></div>");
        //htmlSilent.attr('title', Maco.explainerTranslations[Maco.translationLang].explainer_256);
        var checkboxSilent = new west.gui.Checkbox()
            .setLabel("<span> Make sound </span>")
            .setSelected(!Maco.settings.notifications.silent)
            .setCallback(function() {
                Maco.settings.notifications.silent = !Maco.settings.notifications.silent;
                saveAllConfirmation();
            });
        htmlSilent.append(checkboxSilent.getMainDiv());

        var htmlRequireInteraction = $("<div></div>");
        //htmlRequireInteraction.attr('title', Maco.explainerTranslations[Maco.translationLang].explainer_257);
        var checkboxRequireInteraction = new west.gui.Checkbox()
            .setLabel("<span> Require interaction </span>")
            .setSelected(Maco.settings.notifications.requireInteraction)
            .setCallback(function() {
                Maco.settings.notifications.requireInteraction = !Maco.settings.notifications.requireInteraction;
                saveAllConfirmation();
            });
        htmlRequireInteraction.append(checkboxRequireInteraction.getMainDiv());

        // OPTIONS
        var htmlNotifyError = $("<div style='margin-bottom: 4px;'></div>");
        //htmlNotifyError.attr('title', Maco.explainerTranslations[Maco.translationLang].explainer_258);
        var checkboxNotifyError = new west.gui.Checkbox()
            .setLabel("<span> Error occurs (important) </span>")
            .setSelected(Maco.settings.notifications.error)
            .setCallback(function() {
                Maco.settings.notifications.error = !Maco.settings.notifications.error;
                saveAllConfirmation();
            });
        htmlNotifyError.append(checkboxNotifyError.getMainDiv());

        var htmlNotifyStopped = $("<div style='margin-bottom: 4px;'></div>");
        //htmlNotifyStopped.attr('title', Maco.explainerTranslations[Maco.translationLang].explainer_259);
        var checkboxNotifyStopped = new west.gui.Checkbox()
            .setLabel("<span> Script has Stopped </span>")
            .setSelected(Maco.settings.notifications.stopped)
            .setCallback(function() {
                Maco.settings.notifications.stopped = !Maco.settings.notifications.stopped;
                saveAllConfirmation();
            });
        htmlNotifyStopped.append(checkboxNotifyStopped.getMainDiv());

        var htmlNotifySleep = $("<div style='margin-bottom: 4px;'></div>");
        //htmlNotifySleep.attr('title', Maco.explainerTranslations[Maco.translationLang].explainer_260);
        var checkboxNotifySleep = new west.gui.Checkbox()
            .setLabel("<span> Sleep regenerating starts</span>")
            .setSelected(Maco.settings.notifications.sleep)
            .setCallback(function() {
                Maco.settings.notifications.sleep = !Maco.settings.notifications.sleep;
                saveAllConfirmation();
            });
        htmlNotifySleep.append(checkboxNotifySleep.getMainDiv());

        var htmlNotifyBattle = $("<div style='margin-bottom: 4px;'></div>");
        //htmlNotifyBattle.attr('title', Maco.explainerTranslations[Maco.translationLang].explainer_261);
        var checkboxNotifyBattle = new west.gui.Checkbox()
            .setLabel("<span> Fort Battle starts </span>")
            .setSelected(Maco.settings.notifications.battle)
            .setCallback(function() {
                Maco.settings.notifications.battle = !Maco.settings.notifications.battle;
                saveAllConfirmation();
            });
        htmlNotifyBattle.append(checkboxNotifyBattle.getMainDiv());

        var htmlNotifyBattlePrepare = $("<div style='margin-bottom: 4px;'></div>");
        //htmlNotifyBattlePrepare.attr('title', Maco.explainerTranslations[Maco.translationLang].explainer_262);
        var checkboxNotifyBattlePrepare = new west.gui.Checkbox()
            .setLabel("<span> Fort Battle prepare </span>")
            .setSelected(Maco.settings.notifications.battle_prep)
            .setCallback(function() {
                Maco.settings.notifications.battle_prep = !Maco.settings.notifications.battle_prep;
                saveAllConfirmation();
            });
        htmlNotifyBattlePrepare.append(checkboxNotifyBattlePrepare.getMainDiv());

        var htmlNotifyDuel = $("<div></div>");
        //htmlNotifyDuel.attr('title', Maco.explainerTranslations[Maco.translationLang].explainer_263);
        var checkboxNotifyDuel = new west.gui.Checkbox()
            .setLabel("<span> Duel protection ends </span>")
            .setSelected(Maco.settings.notifications.duel)
            .setCallback(function() {
                Maco.settings.notifications.duel = !Maco.settings.notifications.duel;
                saveAllConfirmation();
            });
        htmlNotifyDuel.append(checkboxNotifyDuel.getMainDiv());

        htmlOptions.append(htmlSilent);
        htmlOptions.append(htmlRequireInteraction);
        htmlOptions.append("<br><br>");
        htmlOptions.append("<span><b>Notify when:</b></span>");
        htmlOptions.append("<br><br>");
        htmlOptions.append(htmlNotifyError);
        htmlOptions.append(htmlNotifyStopped);
        htmlOptions.append(htmlNotifySleep);
        htmlOptions.append(htmlNotifyBattle);
        htmlOptions.append(htmlNotifyBattlePrepare);
        htmlOptions.append(htmlNotifyDuel);

        htmlSkel.append(htmlEnable);
        htmlSkel.append(htmlOptions);
        htmlSkel.append(buttonTestDiv);
        return htmlSkel;
    };
    Maco.createTownBuildGui = function(cityhallData) {
        var htmlSkel = $("<div id=\'build_overview'\ style = \'margin: 30px; margin-top: 10px;'\></div>");
        const saveAllConfirmation = () => Maco.debouncedSaveAll(100, () => new UserMessage("Saved successfully.", UserMessage.TYPE_SUCCESS).show());

        function createComboboxBuildings(data) {
            let combobox = new west.gui.Combobox().setWidth(120);

            if (typeof data === "string") {
                combobox.addItem("string", data);
            } else if (data.buildings && Array.isArray(data.buildings)) {
                data.buildings.forEach(building => {
                    if (building.infinite || building.stage < building.maxStage) {
                        combobox.addItem(building.key, building.name);
                    }
                });
            }

            combobox = combobox.select(Maco.build.building);
            combobox.addListener(function(building) {
                Maco.build.building = building;
                saveAllConfirmation();
            });

            return combobox.getMainDiv();
        }

        function createComboboxInterval() {
            let combobox = new west.gui.Combobox().setWidth(60);
            combobox.addItem(900, "15 min");
            combobox.addItem(1800, "30 min");
            combobox.addItem(3600, "1 hour");

            combobox = combobox.select(Maco.build.interval);
            combobox.addListener(function(interval) {
                Maco.build.interval = interval;
                saveAllConfirmation();
            });

            return combobox.getMainDiv();
        }

        var htmlEnable = $("<div style='display: flex; align-items: center; width: fit-content; height: 26px; margin-bottom:3px;'></div>");
        htmlEnable.attr('title', Maco.explainerTranslations[Maco.translationLang].explainer_28);
        var checkboxEnable = new west.gui.Checkbox()
            .setLabel("Enable Town Build")
            .setSelected(Maco.build.allowed)
            .setCallback(function() {
                Maco.build.allowed = !Maco.build.allowed;
                if (Maco.build.allowed) {
                    $("#build_set_combobox").css('visibility','visible');
                    $("#options_container").css('visibility','visible');
                    $("#button_test_notification").css('visibility','visible');
                } else {
                    $("#build_set_combobox").css('visibility','hidden');
                    $("#options_container").css('visibility','hidden');
                    $("#button_test_notification").css('visibility','hidden');
                }
                saveAllConfirmation();
            });
        htmlEnable.append(checkboxEnable.getMainDiv());

        // Button
        var buttonBuild = new west.gui.Button((Maco.currentState === 7) ? "Stop Build" : "Start Build now", function() {
            if (Maco.currentState === 7) {
                Maco.isRunning = false;
                Maco.currentState = 0;
                Maco.refreshTab("townBuild");
            } else if (Maco.canBuild()) {
                Maco.buildTownBuilding(Maco.build.building, Maco.build.interval, Maco.build.hoursAmount);
            } else {
                new UserMessage("You are gay :)", UserMessage.TYPE_ERROR).show();
                return;
            }
        }).setWidth(120);
        var buttonBuildDiv = buttonBuild.getMainDiv();
        buttonBuildDiv.id = 'button_test_notification';
        $(buttonBuildDiv).css({
            'position': 'absolute',
            'top': '160px',
            'left': '50px',
            'visibility': (Maco.build.allowed) ? 'visible' : 'hidden'
        });

        // OPTIONS
        var htmlOptions = $("<div id='options_container'></div>").css({
            'display': 'inline-block',
            'position': 'relative',
            'left': '25px',
            'visibility': (Maco.build.allowed) ? 'visible' : 'hidden'
        });

        var htmlNightBuild = $("<div style='display: flex; align-items: center; width: fit-content; height: 35px;'></div>");
        htmlNightBuild.attr('title', Maco.explainerTranslations[Maco.translationLang].explainer_29);
        var checkboxNightBuild = new west.gui.Checkbox()
            .setLabel("<span> Build over night </span>")
            .setSelected(Maco.build.nightBuild)
            .setCallback(function() {
                Maco.build.nightBuild = !Maco.build.nightBuild;
                saveAllConfirmation();
            });
        htmlNightBuild.append(checkboxNightBuild.getMainDiv());

        var htmlBuildDurationTextField = $("<div id='build_duration_textfield'></div>").css({
            'display': 'inline-block',
        });
        const hoursTextfield = new west.gui.Textfield("build_duration_textField").onlyNumeric().setValue(Maco.build.hoursAmount).setWidth(40);
        const textfieldDiv = hoursTextfield.getMainDiv();
        $(textfieldDiv).css({
            display: "inline-block",
            position: "relative",
            marginRight: "10px",
        });
        $(textfieldDiv).find("input").on("change", function() {
            const newValue = $(this).val();
            Maco.build.hoursAmount = parseInt(newValue, 10);
            //Maco.build.hoursAmount = hoursTextfield.getValue(); // This also works
            saveAllConfirmation();
        });
        htmlBuildDurationTextField.append("<span> Hours amount to build: </span>");
        htmlBuildDurationTextField.append(textfieldDiv);

        var buildSetCombobox = Maco.addComboboxSetItems(new west.gui.Combobox().setWidth(120), Maco.build.set, 'AUTO_CALC')
            .addListener(function(value) {
                Maco.build.set = value;
                saveAllConfirmation();
            });
        var buildSetDiv = $("<div id='build_set_combobox'><span> Set: </span></div>").css({
            'position': 'absolute',
            'top': '160px',
            'left': '339px',
            'visibility': (Maco.build.allowed) ? 'visible' : 'hidden'
        });
        buildSetDiv.append(buildSetCombobox.getMainDiv());

        htmlOptions.append(htmlBuildDurationTextField);
        htmlOptions.append(createComboboxInterval());
        htmlOptions.append("<span style='margin-right: 10px;'> </span>");
        htmlOptions.append(createComboboxBuildings(cityhallData));
        htmlSkel.append("<br>");
        htmlOptions.append(htmlNightBuild);

        // Assemble all
        htmlSkel.append(htmlEnable);
        htmlSkel.append("<br>");
        htmlSkel.append(htmlOptions);
        htmlSkel.append(buttonBuildDiv);
        htmlSkel.append(buildSetDiv);
        return htmlSkel;
    };
    Maco.loadCityHall = function(callback) {
        Ajax.remoteCall(
            'building_cityhall', 
            '', 
            { town_id: Character.homeTown.town_id }, 
            function(json) {
                if (json && typeof callback === 'function') {
                    callback(json);
                } else {
                    console.error("Maco.loadCityHall: Invalid JSON response or callback not provided.");
                }
            }
        );
    };
    Maco.createStatisticsGui = function() {
        var htmlSkel = $("<div id=\'statistics_overview'\ style = \'margin-left: 10px; margin-top: 5px; user-select: text'\></div>");

        const runTimeInHours = Maco.stats.session.runTime / 3600;
        const totalWaitingTime = Maco.stats.session.consumableWaitingTime + Maco.stats.session.sleepTime;
        let travelTimePercent = (Maco.stats.session.travelTime / Maco.stats.session.runTime) * 100;
        let waitingTimePercent = (totalWaitingTime / Maco.stats.session.runTime) * 100;
        let xpPerHour = Math.round(Maco.stats.session.xp / runTimeInHours);
        let moneyPerHour = Math.round(Maco.stats.session.money / runTimeInHours);
        let xpPerJob = Math.round(Maco.stats.session.xp / Maco.stats.session.jobs);

        travelTimePercent = isNaN(travelTimePercent) ? 0 : travelTimePercent.toFixed(2);
        waitingTimePercent = isNaN(waitingTimePercent) ? 0 : waitingTimePercent.toFixed(2);
        xpPerHour = isNaN(xpPerHour) ? 0 : xpPerHour;
        moneyPerHour = isNaN(moneyPerHour) ? 0 : moneyPerHour;
        xpPerJob = isNaN(xpPerJob) || xpPerJob < 0 ? 0 : xpPerJob;

        var travelTimeText = "Travel time: &nbsp;" + formatTime(Maco.stats.session.travelTime, false) + "&nbsp; = &nbsp;<b>" + travelTimePercent + "%</b>";
        var waitingTimeText = "Waiting time: &nbsp;" + formatTime(totalWaitingTime, false) + "&nbsp; = &nbsp;<b>" + waitingTimePercent + "%</b>";
        var xpPerHourText = "&nbsp;&nbsp;&nbsp; | &nbsp;&nbsp;&nbsp;" + formatNumber(xpPerHour) + "&nbsp;&nbsp; xp / h";
        var moneyPerHourText = "&nbsp;&nbsp;&nbsp; | &nbsp;&nbsp;&nbsp;" + formatNumber(moneyPerHour) + "&nbsp;&nbsp; $ / h";
        var xpPerJobText = "&nbsp;&nbsp;&nbsp; | &nbsp;&nbsp;&nbsp;" + formatNumber(xpPerJob) + "&nbsp;&nbsp; xp / job";

        let lineBreak = $("<br><br>");
        let containerDiv = $("<div style='display: flex; align-items: baseline;'></div>");
        containerDiv.append($("<span>Session runtime: &nbsp;<b>" + formatTime(Maco.stats.session.runTime, false) + "</b></span>"));
        containerDiv.append("<span style='margin-left: 30px;'>" + "Including:" + "</span>");
        let nestedDiv = $("<div style='display: flex; flex-direction: column; margin-left: 10px;'></div>");
        nestedDiv.append($("<span>" + travelTimeText + "</span>"));
        if (totalWaitingTime > 0) {
            nestedDiv.append($("<span style='margin-top: 3px;'>" + waitingTimeText + "</span>"));
            lineBreak = $("<br>");
        }
        containerDiv.append(nestedDiv);
        htmlSkel.append(containerDiv);
        htmlSkel.append(lineBreak);

        htmlSkel.append($("<div style='margin-bottom: 2px;'><span>XP in this session: &nbsp;&nbsp;<b>" + formatNumber(Maco.stats.session.xp) + xpPerHourText + "</b></span></div>"));
        htmlSkel.append($("<span>XP in total: &nbsp;" + formatNumber(Maco.stats.total.xp) + "</span><br>"));
        htmlSkel.append($("<br>"));

        htmlSkel.append($("<div style='margin-bottom: 2px;'><span>Money in this session: &nbsp;&nbsp;<b>" + formatNumber(Maco.stats.session.money) + moneyPerHourText + "</b></span></div>"));
        htmlSkel.append($("<span>Money in total: &nbsp;" + formatNumber(Maco.stats.total.money) + "</span><br>"));
        htmlSkel.append($("<br>"));

        htmlSkel.append($("<div style='margin-bottom: 2px;'><span>Jobs in this session: &nbsp;&nbsp;<b>" + formatNumber(Maco.stats.session.jobs) + xpPerJobText + "</b></span></div>"));
        htmlSkel.append($("<span>Jobs in total: &nbsp;" + formatNumber(Maco.stats.total.jobs) + "</span><br>"));

        if (Maco.diagnostics.reloadReasons && Maco.diagnostics.reloadReasons.length > 0) {
            htmlSkel.append($("<br><br>"));
            htmlSkel.append($("<span><b>Last auto-refresh:</b> &nbsp;</span>"));
            htmlSkel.append($("<span style='margin-left: 2px;'>" + Maco.diagnostics.reloadReasons[0] + "</span><br>"));
            for (let i = 1; i < Math.min(5, Maco.diagnostics.reloadReasons.length); i++) {
                htmlSkel.append($("<span style='margin-left: 120px;'>" + Maco.diagnostics.reloadReasons[i] + "</span><br>"));
            }
            if (Maco.diagnostics.reloadReasons.length > 5) {
                htmlSkel.append($("<span style='margin-left: 120px;'><b>...</b></span><br>"));
            }
        }
        var buttonResetSession = new west.gui.Button("Reset session stats", function() {
            Maco.stats.session.consumableWaitingTime = 0;
            Maco.stats.session.sleepTime = 0;
            Maco.stats.session.travelTime = 0;
            Maco.stats.session.runTime = 0;
            Maco.stats.session.money = 0;
            Maco.stats.session.jobs = 0;
            Maco.stats.session.xp = 0;
            Maco.startTime = new Date();
            Maco.diagnostics.consumablesUsed = [];
            Maco.diagnostics.reloadReasons = [];
            Maco.diagnostics.waitingReasons = [];
            Maco.debouncedSaveAll(0);
            Maco.selectTab("stats");
        });
        var buttonResetStats = new west.gui.Button("Reset all stats", function() {
            Maco.stats.total.money = 0;
            Maco.stats.total.jobs = 0;
            Maco.stats.total.xp = 0;
            Maco.localStorageSet('statsTime', getFormattedLocalDate());
            buttonResetSession.click();
        });
        var buttonResetSessionDiv = buttonResetSession.getMainDiv();
        $(buttonResetSessionDiv).css({
            'position': 'absolute',
            'bottom': '20px',
            'right': '50px'
        });
        var buttonResetStatsDiv = buttonResetStats.getMainDiv();
        $(buttonResetStatsDiv).css({
            'position': 'absolute',
            'bottom': '20px',
            'left': '50px'
        });
        var statsTime = Maco.localStorageGet('statsTime');
        if (statsTime) {
            var timestampText = "Last reset: " + statsTime + "";
            var timestampSpan = $("<span></span>").text(timestampText);
            htmlSkel.append($("<div></div>").css({
                'position': 'absolute',
                'bottom': '0px',
                'left': '54px'
            }).append(timestampSpan));
        }
        htmlSkel.append(buttonResetSessionDiv);
        htmlSkel.append(buttonResetStatsDiv);
        return htmlSkel;
    };
    Maco.checkAndClickRewardButton = function(collectLowLevel = false) {
        const clickDelay = 1000;
        const dialog = document.querySelector('.tw2gui_dialog.loginbonus');
        if (dialog) {
            const rewardRows = dialog.querySelectorAll('.reward-row');
            const todayRow = dialog.querySelector('.reward-row.today');
            const isLastRow = todayRow === rewardRows[rewardRows.length - 1];
            if (Character.level > 1 && Character.level <= 19 && !isLastRow && !collectLowLevel) {
                $(".tw2gui_dialog_framefix").remove();
                return 0;
            }
            const button = dialog.querySelector('.collect-btn');
            if (button) {
                button.click();
                setTimeout(function() {
                    const confirmButton = document.querySelector('.quest_reward_button.normal');
                    if (confirmButton) {
                        confirmButton.click();
                    }
                }, clickDelay);
            }
        }
        return clickDelay;
    };
    Maco.handleCollectLoginReward = function(collectLowLevel = false) {
        const handleLoginBonus = new Promise((r) => {
            const delay = Maco.checkAndClickRewardButton(collectLowLevel);
            setTimeout(r, delay + 1000);
        });

        handleLoginBonus.then(() => {
            if (Character.level > 19 || collectLowLevel) { // Player.hasLoginBonus
                Maco.forceCollectLoginReward();
            }
        });
    };
    Maco.forceCollectLoginReward = function() {
        Ajax.remoteCall('loginbonus', 'collect', null, function(response) {
            if (response.error) {
                new UserMessage(response.msg).show();
            } else {
                Player.hasLoginBonus = false;
                new UserMessage(
                    response.msg + (response.rewards ? " " + Object.entries(response.rewards).map(([key, value]) => `${key}: ${value}`).join(', ') : ""),
                    UserMessage.TYPE_SUCCESS
                ).show();
            }
        });
    };
    Maco.createMenuIcon = function() {
        const menuimage = 'data:image/png;base64,iVBORw0KGgoAAAANSUhEUgAAABgAAAAYCAYAAADgdz34AAAACXBIWXMAAAsTAAALEwEAmpwYAAAFkUlEQVRIS42V7W9T1x3HP+deYzvGwY7D7JCE5mGYhvCQkOxBHVVMClO6SZ22aUZCU2m3ib2YRKVpfwDLVlWaVK2rtmkvNrWgvehUjRfVoBSJDgKkBUYCaakXoAlOnMROnCfHjh/utc/ZC9tpnBRpP+lI594jfT/3fH/nfK+F/79EaZRLrps/sSwbXwDaurkqDc3jcj2nICClREqptHz+7UQuFy6tPxFeAXA5HAeVEG+ggUBDwNvLyeTZaofj8tdbdrS2N3ibFAqpUFdC4y9EFhNXl1dSv3I6HK9rut4lgEIhb6TSmT6K4DWAaPB6v7mv3vNRX4dflL/pzlik59PJubde7u3WNAWI4oJSiJ8Eujqjy6nOC0OhV757sE2r91QjEBQUvPXh7VtxQx6Px+NjFoBAIKB/eu/u7/o6dguP14fb5yOZWGL3yoroaqoXmlKIsgGq5IWCBpeTFw91aDnDoHV/JwDR8Uf0HvB3nx0YPg68umaRKlno9tXRvPcAl945i9NRha6vs1Z9MS2X3WZD1zTi8Tm+0XuUpVi0ohlrACnzmKZJNpVkbnqS1UQCt9sFCpQouSYUqC8ooiRl2WJhMTbL/MwMedPEMHJIWeyzBWBgYEBWOxxnPn7wuCeTyZD6eJCGurqyCqji/kQJhFhrB6q0JrNpLp/7BzarjbtjkTEJA2sAQCbT6TNDE3Pu0djS7zUBJ30+EAK1zntV8kgUHxFoa71ZzBhcGHmMWSgY0/OJYNY0R6DymKrI/OIfAoHAX+4ND19Sgh5Q3JnL8v6N2xze00ygrQlQFBAML2R5/8YtAm3NBNqeIpOXRJZSv0murr4KmGXRjRdNHT582Bge+k++7G/7njbOX7+Fy+ujZV8HClVsw2qBf12/iVKK8jaFEJJ14rAZwN69e4UQur6tqprd9a1cCY3wixd66el7nvcuXeHzyQh9Pc/Q1NjAiUOd7Gtspr2xifH5a1SGQLE2AY4dO6aqnc6CaZpoQqfB5UTb5qTB5+Xkj4P8+ew7HHn2W+gazHjd1Dqr0IWGaRh8WTxtApw+fZo/vfnmucuffPbc3PICjiob27c5USi26Bqv/OB7CE2AKoqNR8OEJh7ySXg6bLFaBzfIbQb09/fL7u7uv96Pz35ldHbx14dad5A1C+wIP6auuQWtyopCMTYyTHx+gdHZRUIzC3lDt7946tSpj/r7+yv0NgEAhoaGzPbGxj8upo3BKw8ir7sjcx0PIjNomr52VGUhz92pRXJ5+XfDkGcmFyI3NorDEwDBYFBPPgi91t5Y+1KD22EtFPLcn4qX7xygEELw/S4/sWT6eCpT+GF91P3Tm+GxdzdIbQYEg0H9g/Pn+09959mf1TptluWVFYYnlzm638+uA5043DXMhseJTYQZfBThkL/R4qiqstit8TfuxabJZrMVkApATU2N6+LFi/vqrJbnkQVLMpXivaGHnDj6DO3dX6P+q34QGjtbWnk4fIdoMsu10DhH9u9CSbO+3mr9dlSIyUwmc/PLAJrXaX9tl6/+JSmVPRSdp9auY0qJZ/t2drT6i9GBQtMt+A92M3jzNqZU3J+aZ8Uo0OZ/6sTTSv7o6n8fn8xkMv/cCBB2q+XnvXtaLKBIGya3x6Zoqt3GtdEJuo6U73YpWXULI+GZYtAJQeDpnQDWghLWq6Hxl4FNAJSUFmQB3aJTbduCZ6sDbBpj0Ti5dBqbYyvFmIPVxBKzy0l2+9w0elxomkAgyJtmhW5F2KUzxruj07FjOz0uBNDs2cpnkVVqZJ6hqx9S461bi+jo+Od4nXZqt1bh0BTJVAoBjEzE8lKpc2XR9QC5lEj98vqjKWHfMhvUNAEIYolVtjvt/O3CvxGahpLFHSglSefyRBLTuCLx4j9CCJZS6d/mcrkzZdH/AeUGcu6EUJgTAAAAAElFTkSuQmCC';
        const div = $('<div class="ui_menucontainer" />');
        const link = $('<div id="Menu" class="menulink" title="Maco"></div>').css('background-image', 'url(' + menuimage + ')').on('click', function () {Maco.loadMapData(Maco.createWindow);});
        $('#ui_menubar').append((div).append(link).append('<div class="menucontainer_bottom" />'));
    };
    function isProgressBarVisible() {
        const progressBar = document.querySelector('.progress-bar');
        return progressBar && progressBar.offsetParent !== null;
    };
    const documentReady = async function() {
        try {
            const gameURL = /^https:\/\/.*\.the-west\..*\/game\.php/;
            const logoutURL = /^https:\/\/.*\.the-west\..*\/index\.php\?page=logout(?:&|$)/;
            const homeURL = /^https:\/\/www\.the-west\.[a-zA-Z0-9]+(?:\/|\/.*)?$/;

            if (logoutURL.test(document.URL)) {
                globalWindow.location.href = "./";
            } else if (homeURL.test(document.URL)) {
                let isPermaLogged = document.querySelector('#cookieLogged') != null;
                GM_setValue("perma_logged", isPermaLogged);

                const checkboxElement = document.querySelector('#cookie');
                if (checkboxElement) {
                    const observer = new MutationObserver((mutationsList) => {
                        for (const mutation of mutationsList) {
                            if (mutation.type === 'attributes' && mutation.attributeName === 'class') {
                                isPermaLogged = checkboxElement.classList.contains('checked');
                                GM_setValue("perma_logged", isPermaLogged);
                            }
                        }
                    });
                    observer.observe(checkboxElement, { attributes: true });
                }

                const autoLogin = GM_getValue("auto_login", {allowed: false, world: ''});
                setTimeout(function() {
                    if (autoLogin.allowed && document.querySelectorAll('.world_row').length === 0) {
                        Maco.gameLogin(autoLogin.world);
                    }
                }, 2000);
            } else if (gameURL.test(document.URL)) {
                initCss();
                characterId = Character.level > 24 ? Character.playerId : 0;
                Maco.loadSavedData();
                Maco.installHooks();
                Maco.loadAccountSettings();
                Maco.loadSets(function() {});
                if (characterId === 0 || Maco.settings.showMenuIcon) {
                    Maco.createMenuIcon();
                }
                Maco.lastReloadTime = getUTCDate().getTime();
                Maco.loadAlertsFromLocalStorage();
                EventHandler.listen('fort_battle_joined', Maco.updateFortBattles);
                const reloadInfoString = Maco.localStorageGet('reloadData');
                //if (!reloadInfoString) Maco.updateCheck();

                setTimeout(function() {
                    Maco.verifyChatLeave();
                    Maco.sendEventCurrency();
                }, AUTO_START_DELAY - 1000);

                setTimeout(function() {
                    if (Maco.dailyQuests.enabled) {
                        Maco.runDailyQuests();
                    }
                }, 5000 + AUTO_START_DELAY + GAME_LOAD_TIMEOUT);

                setTimeout(function() {
                    if (Maco.settings.skipTutorial && LinearQuestHandler.hasTutorialQuest()) {
                        Maco.skipTutorial();
                    }
                    Maco.checkAndClickRewardButton();
                    Maco.startSpecialConsumableInterval();
                    GM_deleteValue("auto_login");

                    if (reloadInfoString) {
                        const reloadInfo = JSON.parse(reloadInfoString);
                        const reason = reloadInfo.reason;
                        const resumeSession = reloadInfo.auto_start;
                        Maco.diagnostics.reloadReasons.unshift(reason);
                        if (Maco.diagnostics.reloadReasons.length > 30) Maco.diagnostics.reloadReasons.pop();
                        Maco.debouncedSaveAll(0);
                        Maco.localStorageRemove('reloadData');
                        console.log("Auto-reload occured.. Reason: " + reason);
                        console.log(Maco.diagnostics.errorLog && Maco.diagnostics.errorLog.length > 0
                            ? `Last Error: ${Maco.diagnostics.errorLog[0]?.timestamp}, ${Maco.diagnostics.errorLog[0]?.error}`
                            : "No errors logged."
                        );

                        if (resumeSession) {
                            Maco.startReloadObserver();
                            if (document.querySelector('.critical-error') || Maco.invalidSession) return;

                            const loadJobsTimeoutId = setTimeout(function() {
                                if (!isProgressBarVisible()) {
                                    Maco.loadMapData(() => {
                                        setTimeout(Maco.resumeSession, 2000);
                                    });
                                } else {
                                    Maco.reload("Stuck in loading screen. Retrying.. ");
                                }
                            }, GAME_LOAD_TIMEOUT);

                            Maco.loadMapData(() => {
                                clearTimeout(loadJobsTimeoutId);
                                setTimeout(Maco.resumeSession, 2000);
                            });
                        }
                    }
                }, AUTO_START_DELAY);
            }
        } catch (e) {
            const msg = "Exception occured when loading document: ";
            console.error(msg, e.stack);
            if (String(e).toLowerCase().includes("invalid session")) {
                setTimeout(function() {
                    globalWindow.location.reload();
                }, 30000);
            }
            Maco.handleError(e, msg);
        }
    };
    function initCss() {
        //globalWindow.Maco = Maco;
        const customAlertHtml = `<div id="Maco-alertContainer"></div>`;
        const customAlertCss = `
        #Maco-alertContainer {
            position: fixed;
            top: 20%;
            left: 50%;
            transform: translateX(-50%);
            z-index: 9999;
        }
        .Maco-alert {
            background-color: #fff;
            border: 2px solid #ccc;
            border-radius: 5px;
            padding: 20px;
            box-shadow: 0 2px 4px rgba(0, 0, 0, 0.1);
            margin-bottom: 10px;
            width: fit-content;
            min-width: 258px;
            max-width: 700px;
            word-wrap: break-word;
        }
        .alert-message {
            font-size: 16px;
            margin-bottom: 15px;
            user-select: text;
            white-space: pre-wrap;
        }
        .alert-title {
            font-size: 14px;
            color: #424651;
            margin-bottom: 10px;
        }
        .alert-ok {
            background-color: #007bff;
            color: #fff;
            border: none;
            padding: 10px 20px;
            border-radius: 5px;
            cursor: pointer;
        }
        .alert-ok:hover {
            background-color: #0056b3;
        }`;

        // Inject HTML
        const div = document.createElement('div');
        div.innerHTML = customAlertHtml;
        document.body.appendChild(div);

        // Inject CSS
        const style = document.createElement('style');
        style.textContent = customAlertCss;
        document.head.appendChild(style);
    };
    Maco.resumeSession = async function() {
        Maco.handleCollectLoginReward();
        if (Maco.addedJobs.length === 0) {
            const doNightBuild = Maco.canBuild() && Maco.build.nightBuild;
            if ((Maco.settings.nightShiftWorker || doNightBuild) && Maco.swapSilverJobs()) {
                Maco.diagnostics.reloadReasons[0] += "Silver jobs changed.";
                if (await Maco.verifySilverJobs()) {
                    Maco.addedJobs = [];
                    Maco.debouncedSaveAll(0);
                    await wait(timeout_long); // Delayed reload
                    Maco.reload("Silver jobs mismatch. Retrying.. ");
                    return;
                }
                if (doNightBuild) {
                    Maco.buildTownBuilding(Maco.build.building, Maco.build.interval, Maco.build.hoursAmount);
                    return;
                }
            } else if (Maco.canBuild()) {
                Maco.buildTownBuilding(Maco.build.building, Maco.build.interval);
                return;
            } else {
                const altMessage = "No jobs to run."
                Maco.diagnostics.reloadReasons[0] += " " + altMessage;
                Maco.sleep({ dontWakeUp: true, message: altMessage });
                return;
            }
        }
        console.log("Continuing jobs..");
        Maco.handleScriptStart();
    };
    Maco.sendEventCurrency = function() {
        const event_id = Maco.getActiveEventId();
        if (!event_id) return;

        Ajax.remoteCall('friendsbar', 'event_all', {
            event: event_id
        }, response => {
            if (response.error) {
                //MessageError(response.msg).show();
            } else if (extractNumberFromString(response.msg) > 0) {
                MessageSuccess(response.msg).show();
            }
        });
    };
    Maco.getActiveEventId = function() {
        return Object.keys(globalWindow.Game.sesData)[0];
    };
    Maco.leaveChat = function(id) {
        Chat.Router.push(new Chat.Request("setonlinestate", null, {
            room: id,
            state: true
        })).request();

        Chat.MyClient.setRoomState(id, false);
        Chat.Router.push(new Chat.Request("setonlinestate", null, {
            room: id,
            state: false
        })).request();
    };
    Maco.verifyChatLeave = function() {
        const chatChannels = document.querySelectorAll('.chat_channel');
        chatChannels.forEach(channel => {
            const leaveChannelImg = channel.querySelector('.leave_channel');
            if (leaveChannelImg && leaveChannelImg.style.display === 'none') {
                Maco.leaveChat(channel.id);
            }
        });
    };
    Maco.showNotification = function(title, body = "", type = "enabled") {
        if (!Maco.settings.notifications.enabled || !Maco.settings.notifications[type]) return false;

        if (!("Notification" in globalWindow)) { // Check if the Notification API is supported by the browser
            console.warn("%cNotifications not supported in this browser.", 'color: cyan');
            return false;
        }
        if (Notification.permission !== "granted") { // Request permission to display notifications (if not already granted)
            Notification.requestPermission().then(function (permission) {
                if (permission !== "granted") {
                    console.warn("%cNotification permission denied.", 'color: cyan');
                }
            });
            return false;
        }
        // Display the notification
        new Notification(title, {
            silent: Maco.settings.notifications.silent,
            requireInteraction: Maco.settings.notifications.requireInteraction,
            body: body
        });
        return true;
    };
    Maco.showAlert = function(message, addTimestamp = true, savedTimestamp = null, callback = null, openLink = null) {
        const now = new Date().getTime();

        // Check if there's already an alert with the same message in the DOM
        var existingAlerts = document.querySelectorAll('.Maco-alert');
        for (var i = 0; i < existingAlerts.length; i++) {
            if (Maco.isolateAlertMessage(existingAlerts[i].querySelector('.alert-message').innerHTML) === message) {
                // Increment the count if the message already exists
                existingAlerts[i].querySelector('.alert-message').innerHTML = Maco.incrementAlertCount(existingAlerts[i].querySelector('.alert-message').innerHTML);
                existingAlerts[i].style.display = 'block';
                return existingAlerts[i].id;
            }
        }

        // Create a new alert if no matching one exists
        var alertId = 'Maco-alert-' + now;
        var alertDiv = document.createElement('div');
        alertDiv.id = alertId;
        alertDiv.className = 'Maco-alert';

        var titleDiv = document.createElement('div');
        titleDiv.className = 'alert-title';
        
        var messageDiv = document.createElement('div');
        messageDiv.className = 'alert-message';

        titleDiv.innerText = "Maco";
        let timestampString = "";
        if (addTimestamp || savedTimestamp) {
            timestampString = savedTimestamp || timestamp();
            titleDiv.innerText += " - " + timestampString;  // Append timestamp to title
        }

        messageDiv.innerHTML = message;  // Add the main message text

        var okButton = document.createElement('button');
        okButton.className = 'alert-ok';
        okButton.innerText = 'OK';
        okButton.addEventListener('click', function() {
            alertDiv.remove();
            Maco.removeAlertFromLocalStorage(message); // Remove alert from local storage
            if (openLink) {
                window.open(openLink, "_blank");
            }
            if (typeof callback === 'function') {
                try {
                    callback();
                } catch (err) {
                    console.error('Error in Maco.showAlert callback:', err);
                }
            }
        });

        alertDiv.appendChild(titleDiv); // Add timestamp div
        alertDiv.appendChild(messageDiv); // Add message div
        alertDiv.appendChild(okButton); // Add OK button

        document.getElementById('Maco-alertContainer').appendChild(alertDiv);
        alertDiv.style.display = 'block';
        globalWindow.focus();
        Maco.saveAlertToLocalStorage(message, timestampString, openLink); // Save alert to local storage

        return alertId;
    };
    Maco.saveAlertToLocalStorage = function(message, timestamp, openLink) {
        let alerts = JSON.parse(Maco.localStorageGet('alerts')) || [];

        const alertData = { // Add both message and timestamp as an object
            message: message,
            timestamp: timestamp,
            openLink: openLink
        };

        if (!alerts.some(alert => alert.message === message)) { // Avoid duplicate entries
            alerts.push(alertData);
            Maco.localStorageSet('alerts', JSON.stringify(alerts));
        }
    };
    Maco.removeAlertFromLocalStorage = function(message) {
        let alerts = JSON.parse(Maco.localStorageGet('alerts')) || [];
        alerts = alerts.filter(alert => alert.message !== message);
        Maco.localStorageSet('alerts', JSON.stringify(alerts));
    };
    Maco.loadAlertsFromLocalStorage = function() {
        let alerts = JSON.parse(Maco.localStorageGet('alerts')) || [];

        alerts.forEach(alert => {
            Maco.showAlert(alert.message, false, alert.timestamp, alert.openLink); // Pass the saved timestamp
        });
    };
    Maco.isolateAlertMessage = function(fullMessage) {
        const leadingCountPattern = /^\(\d+\)\s*/; // Regex to match a number in parentheses at the start
        return fullMessage.replace(leadingCountPattern, '');
    };
    Maco.incrementAlertCount = function(message) {
        const countPattern = /^\((\d+)\)\s*/; // Regex to match a number in parentheses at the start of the string

        let match = message.match(countPattern);

        if (match) { // Extract the number, increment it, and replace the original part with the incremented value
            let count = parseInt(match[1], 10); // Convert matched string to number
            count += 1; // Increment the number
            return message.replace(countPattern, `(${count})  `);
        } else {
            return `(2)  ` + message; // No number found at the start, prepend with (2)
        }
    };
    Maco.startAnimationRemoveObserver = function() {
        const workContainer = document.getElementById('ui_workcontainer');

        function updateStyle() {
            if (TaskQueue.queue.length > 0) {
                workContainer.style.cssText = '';
            } else {
                workContainer.style.cssText = 'display: none;';
            }
        }

        queueAnimationObserver = new MutationObserver(mutations => {
            mutations.forEach(mutation => {
                if (mutation.attributeName === 'style') {
                    const currentStyle = workContainer.style.cssText.trim();
                    if (currentStyle !== '' && currentStyle !== 'display: none;') {
                        updateStyle();
                    }
                }
            });
        });

        queueAnimationObserver.observe(workContainer, {
            attributes: true, // Listen for attribute changes
            attributeFilter: ['style'] // Only listen for changes to the style attribute
        });
    };
    // Create a dummy invisible button once
    function createDummyButton() {
        let dummy = document.getElementById("west-btn-exercise");
        if (!dummy) {
            dummy = document.createElement("button");
            dummy.id = "west-btn-exercise";
            dummy.style.position = "absolute";
            dummy.style.left = "-9999px"; // hide offscreen
            dummy.style.top = "-9999px";
            dummy.style.width = "1px";
            dummy.style.height = "1px";
            dummy.style.opacity = "0";
            document.body.appendChild(dummy);
        }
        return dummy;
    }

    // Simulate a human-like click on the dummy button
    function fakeClick(element) {
        if (!element) return;
        const rect = element.getBoundingClientRect();
        const x = rect.left + rect.width / 2;
        const y = rect.top + rect.height / 2;

        const options = {
            bubbles: true,
            cancelable: true,
            view: element.ownerDocument.defaultView,
            clientX: x,
            clientY: y
        };

        element.dispatchEvent(new MouseEvent("mousedown", options));
        setTimeout(() => {
            element.dispatchEvent(new MouseEvent("mouseup", options));
            element.dispatchEvent(new MouseEvent("click", options));
        }, 50 + Math.random() * 150); // human-like delay
    }

    /** Dispatch a small random mousemove event (to feel alive). */
    function fakeMouseMove() {
        document.dispatchEvent(new MouseEvent("mousemove", {
            bubbles: true,
            clientX: Math.random() * window.innerWidth,
            clientY: Math.random() * window.innerHeight
        }));
    }

    (function installKeepAliveController() {
        const dummy = createDummyButton();

        let timerId = null;
        let running = false;

        // returns random delay between min and max (ms)
        function randomDelay(minMs = 40_000, maxMs = 70_000) {
            return Math.floor(minMs + Math.random() * (maxMs - minMs));
        }

        // schedule next tick with random delay; uses recursive setTimeout so each tick can vary
        function scheduleNextTick() {
            timerId = setTimeout(async () => {
                try {
                    fakeMouseMove();
                    // small randomized extra jitter before clicking
                    await new Promise(r => setTimeout(r, 20 + Math.random() * 80));
                    fakeClick(dummy);
                } catch (e) {
                    // swallow errors so runner continues
                    console.error("keepAlive tick error", e);
                }
                // schedule again if still running
                if (running) scheduleNextTick();
            }, randomDelay());
        }

        // start controller
        function start() {
            if (running) return;
            running = true;
            // first tick quickly so you don't wait full interval on start (optional)
            scheduleNextTick();
        }

        // stop controller
        function stop() {
            running = false;
            if (timerId != null) {
                clearTimeout(timerId);
                timerId = null;
            }
        }

        // Expose control on Maco (or window) so other code can toggle
        if (typeof Maco !== "object") throw new Error("Maco not defined yet");
        Maco.keepAlive = { start, stop, isRunning: () => running };
    })();
    Maco.debouncedSaveAll = debounce(Maco.saveAll, 0);
    $(document).ready(documentReady);
})();
