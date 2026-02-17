# TsadeEngine

## Description

TsadeEngine は直観主義命題論理の中で与えられた定理を検証する遺伝的アルゴリズムを用いた証明探索エンジンです。

今は一階述語論理の導入を進めています。

## Usage

### For single corpus

```bash
# basic
tsade-engine single --theorem Curry --unicode

# save
tsade-engine single --theorem Flip --save flip.tg --unicode

# load
tsade-engine single --theorem Comp --load flip.tg --unicode
```

### For all corpus

```bash
# full
tsade-engine all-corpus --unicode
```

### Help

```bash
tsade-engine --help
```

## Name Origin

> (ツァディ、ヘブライ語: צד״י, צָדִי ṣade) はヘブライ文字の18番目に位置する文字。ヘブライ数字の数価は90。文字名はツァディク (צדיק、「正しい者」を意味する) とも呼ばれる。
>
> \- [Wikipedia](https://ja.wikipedia.org/wiki/%D7%A6)

## License

MIT License
